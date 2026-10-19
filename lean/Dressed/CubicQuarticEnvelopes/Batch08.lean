import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0256 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-19/2048), (-21/2048), (-77/8192), (-27/8192)]

def upper0256 : ℚ := (85197/81920000000000)

def plusWeights0256 : Fin 11 → ℚ := ![(85197/81920000000000), (85197/8192000000000), (766773/16384000000000), (255591/2048000000000), (1789137/8192000000000), (5367411/20480000000000), (1789137/8192000000000), (253691/2048000000000), (719493/16384000000000), (379/51200000000), 0]

def minusWeights0256 : Fin 11 → ℚ := ![(85197/81920000000000), (85197/8192000000000), (766773/16384000000000), (255591/2048000000000), (1789137/8192000000000), (5367411/20480000000000), (1789137/8192000000000), (257491/2048000000000), (814053/16384000000000), (54877/4096000000000), (85197/40960000000000)]

theorem checked0256 :
    (∀ i, 0 ≤ plusWeights0256 i) ∧
    (∀ i, 0 ≤ minusWeights0256 i) ∧
    (∀ i, plusCoefficients coefficients0256 upper0256 i = powerCoefficients10 plusWeights0256 i) ∧
    (∀ i, minusCoefficients coefficients0256 upper0256 i = powerCoefficients10 minusWeights0256 i) := by
  decide +kernel

theorem bound0256 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0256 g| ≤ (upper0256 : ℝ) :=
  abs_of_coefficients coefficients0256 upper0256 powerCoefficients10 plusWeights0256 minusWeights0256
    checked0256.1 checked0256.2.1 checked0256.2.2.1 checked0256.2.2.2
    (power_identity10 plusWeights0256) (power_identity10 minusWeights0256) g hg hmax

def envelope0256 : Envelope := ⟨coefficients0256, upper0256, bound0256⟩

def coefficients0257 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/8192), (175/32768), (175/65536), (6125/524288)]

def upper0257 : ℚ := (35999/41943040000000)

def plusWeights0257 : Fin 11 → ℚ := ![(35999/41943040000000), (35999/4194304000000), (323991/8388608000000), (107997/1048576000000), (755979/4194304000000), (2267937/10485760000000), (755979/4194304000000), (107037/1048576000000), (301399/8388608000000), (124691/20971520000000), 0]

def minusWeights0257 : Fin 11 → ℚ := ![(35999/41943040000000), (35999/4194304000000), (323991/8388608000000), (107997/1048576000000), (755979/4194304000000), (2267937/10485760000000), (755979/4194304000000), (108957/1048576000000), (346583/8388608000000), (235299/20971520000000), (35999/20971520000000)]

theorem checked0257 :
    (∀ i, 0 ≤ plusWeights0257 i) ∧
    (∀ i, 0 ≤ minusWeights0257 i) ∧
    (∀ i, plusCoefficients coefficients0257 upper0257 i = powerCoefficients10 plusWeights0257 i) ∧
    (∀ i, minusCoefficients coefficients0257 upper0257 i = powerCoefficients10 minusWeights0257 i) := by
  decide +kernel

theorem bound0257 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0257 g| ≤ (upper0257 : ℝ) :=
  abs_of_coefficients coefficients0257 upper0257 powerCoefficients10 plusWeights0257 minusWeights0257
    checked0257.1 checked0257.2.1 checked0257.2.2.1 checked0257.2.2.2
    (power_identity10 plusWeights0257) (power_identity10 minusWeights0257) g hg hmax

def envelope0257 : Envelope := ⟨coefficients0257, upper0257, bound0257⟩

def coefficients0258 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/8192), (525/32768), (525/65536), (2625/262144)]

def upper0258 : ℚ := (15651/20971520000000)

def plusWeights0258 : Fin 11 → ℚ := ![(15651/20971520000000), (15651/2097152000000), (140859/4194304000000), (46953/524288000000), (328671/2097152000000), (986013/5242880000000), (328671/2097152000000), (46473/524288000000), (130011/4194304000000), (52899/10485760000000), 0]

def minusWeights0258 : Fin 11 → ℚ := ![(15651/20971520000000), (15651/2097152000000), (140859/4194304000000), (46953/524288000000), (328671/2097152000000), (986013/5242880000000), (328671/2097152000000), (47433/524288000000), (151707/4194304000000), (103611/10485760000000), (15651/10485760000000)]

theorem checked0258 :
    (∀ i, 0 ≤ plusWeights0258 i) ∧
    (∀ i, 0 ≤ minusWeights0258 i) ∧
    (∀ i, plusCoefficients coefficients0258 upper0258 i = powerCoefficients10 plusWeights0258 i) ∧
    (∀ i, minusCoefficients coefficients0258 upper0258 i = powerCoefficients10 minusWeights0258 i) := by
  decide +kernel

theorem bound0258 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0258 g| ≤ (upper0258 : ℝ) :=
  abs_of_coefficients coefficients0258 upper0258 powerCoefficients10 plusWeights0258 minusWeights0258
    checked0258.1 checked0258.2.1 checked0258.2.2.1 checked0258.2.2.2
    (power_identity10 plusWeights0258) (power_identity10 minusWeights0258) g hg hmax

def envelope0258 : Envelope := ⟨coefficients0258, upper0258, bound0258⟩

def coefficients0259 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/8192), (525/32768), (525/65536), (17625/262144)]

def upper0259 : ℚ := (15531/20971520000000)

def plusWeights0259 : Fin 11 → ℚ := ![(15531/20971520000000), (15531/2097152000000), (139779/4194304000000), (46593/524288000000), (326151/2097152000000), (978453/5242880000000), (326151/2097152000000), (46113/524288000000), (128931/4194304000000), (52299/10485760000000), 0]

def minusWeights0259 : Fin 11 → ℚ := ![(15531/20971520000000), (15531/2097152000000), (139779/4194304000000), (46593/524288000000), (326151/2097152000000), (978453/5242880000000), (326151/2097152000000), (47073/524288000000), (150627/4194304000000), (103011/10485760000000), (15531/10485760000000)]

theorem checked0259 :
    (∀ i, 0 ≤ plusWeights0259 i) ∧
    (∀ i, 0 ≤ minusWeights0259 i) ∧
    (∀ i, plusCoefficients coefficients0259 upper0259 i = powerCoefficients10 plusWeights0259 i) ∧
    (∀ i, minusCoefficients coefficients0259 upper0259 i = powerCoefficients10 minusWeights0259 i) := by
  decide +kernel

theorem bound0259 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0259 g| ≤ (upper0259 : ℝ) :=
  abs_of_coefficients coefficients0259 upper0259 powerCoefficients10 plusWeights0259 minusWeights0259
    checked0259.1 checked0259.2.1 checked0259.2.2.1 checked0259.2.2.2
    (power_identity10 plusWeights0259) (power_identity10 minusWeights0259) g hg hmax

def envelope0259 : Envelope := ⟨coefficients0259, upper0259, bound0259⟩

def coefficients0260 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-37/4096), (-43/4096), (-59/4096), (-187/32768)]

def upper0260 : ℚ := (335307/327680000000000)

def plusWeights0260 : Fin 11 → ℚ := ![(335307/327680000000000), (335307/32768000000000), (3017763/65536000000000), (1005921/8192000000000), (7041447/32768000000000), (21124341/81920000000000), (7041447/32768000000000), (998521/8192000000000), (2833283/65536000000000), (47831/6553600000000), 0]

def minusWeights0260 : Fin 11 → ℚ := ![(335307/327680000000000), (335307/32768000000000), (3017763/65536000000000), (1005921/8192000000000), (7041447/32768000000000), (21124341/81920000000000), (7041447/32768000000000), (1013321/8192000000000), (3202243/65536000000000), (431459/32768000000000), (335307/163840000000000)]

theorem checked0260 :
    (∀ i, 0 ≤ plusWeights0260 i) ∧
    (∀ i, 0 ≤ minusWeights0260 i) ∧
    (∀ i, plusCoefficients coefficients0260 upper0260 i = powerCoefficients10 plusWeights0260 i) ∧
    (∀ i, minusCoefficients coefficients0260 upper0260 i = powerCoefficients10 minusWeights0260 i) := by
  decide +kernel

theorem bound0260 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0260 g| ≤ (upper0260 : ℝ) :=
  abs_of_coefficients coefficients0260 upper0260 powerCoefficients10 plusWeights0260 minusWeights0260
    checked0260.1 checked0260.2.1 checked0260.2.2.1 checked0260.2.2.2
    (power_identity10 plusWeights0260) (power_identity10 minusWeights0260) g hg hmax

def envelope0260 : Envelope := ⟨coefficients0260, upper0260, bound0260⟩

def coefficients0261 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/1024), (-11/1024), (-167/4096), (-77/4096)]

def upper0261 : ℚ := (42147/40960000000000)

def plusWeights0261 : Fin 11 → ℚ := ![(42147/40960000000000), (42147/4096000000000), (379323/8192000000000), (126441/1024000000000), (885087/4096000000000), (2655261/10240000000000), (885087/4096000000000), (125541/1024000000000), (356843/8192000000000), (303/40960000000), 0]

def minusWeights0261 : Fin 11 → ℚ := ![(42147/40960000000000), (42147/4096000000000), (379323/8192000000000), (126441/1024000000000), (885087/4096000000000), (2655261/10240000000000), (885087/4096000000000), (127341/1024000000000), (401803/8192000000000), (26997/2048000000000), (42147/20480000000000)]

theorem checked0261 :
    (∀ i, 0 ≤ plusWeights0261 i) ∧
    (∀ i, 0 ≤ minusWeights0261 i) ∧
    (∀ i, plusCoefficients coefficients0261 upper0261 i = powerCoefficients10 plusWeights0261 i) ∧
    (∀ i, minusCoefficients coefficients0261 upper0261 i = powerCoefficients10 minusWeights0261 i) := by
  decide +kernel

theorem bound0261 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0261 g| ≤ (upper0261 : ℝ) :=
  abs_of_coefficients coefficients0261 upper0261 powerCoefficients10 plusWeights0261 minusWeights0261
    checked0261.1 checked0261.2.1 checked0261.2.2.1 checked0261.2.2.2
    (power_identity10 plusWeights0261) (power_identity10 minusWeights0261) g hg hmax

def envelope0261 : Envelope := ⟨coefficients0261, upper0261, bound0261⟩

def coefficients0262 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/1024), (-11/1024), (-67/4096), (-27/4096)]

def upper0262 : ℚ := (41097/40960000000000)

def plusWeights0262 : Fin 11 → ℚ := ![(41097/40960000000000), (41097/4096000000000), (369873/8192000000000), (123291/1024000000000), (863037/4096000000000), (2589111/10240000000000), (863037/4096000000000), (122391/1024000000000), (347393/8192000000000), (587/81920000000), 0]

def minusWeights0262 : Fin 11 → ℚ := ![(41097/40960000000000), (41097/4096000000000), (369873/8192000000000), (123291/1024000000000), (863037/4096000000000), (2589111/10240000000000), (863037/4096000000000), (124191/1024000000000), (392353/8192000000000), (13211/1024000000000), (41097/20480000000000)]

theorem checked0262 :
    (∀ i, 0 ≤ plusWeights0262 i) ∧
    (∀ i, 0 ≤ minusWeights0262 i) ∧
    (∀ i, plusCoefficients coefficients0262 upper0262 i = powerCoefficients10 plusWeights0262 i) ∧
    (∀ i, minusCoefficients coefficients0262 upper0262 i = powerCoefficients10 minusWeights0262 i) := by
  decide +kernel

theorem bound0262 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0262 g| ≤ (upper0262 : ℝ) :=
  abs_of_coefficients coefficients0262 upper0262 powerCoefficients10 plusWeights0262 minusWeights0262
    checked0262.1 checked0262.2.1 checked0262.2.2.1 checked0262.2.2.2
    (power_identity10 plusWeights0262) (power_identity10 minusWeights0262) g hg hmax

def envelope0262 : Envelope := ⟨coefficients0262, upper0262, bound0262⟩

def coefficients0263 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/1024), (-11/1024), (-109/8192), (-83/16384)]

def upper0263 : ℚ := (163863/163840000000000)

def plusWeights0263 : Fin 11 → ℚ := ![(163863/163840000000000), (163863/16384000000000), (1474767/32768000000000), (491589/4096000000000), (3441123/16384000000000), (10323369/40960000000000), (3441123/16384000000000), (487989/4096000000000), (1384847/32768000000000), (4677/655360000000), 0]

def minusWeights0263 : Fin 11 → ℚ := ![(163863/163840000000000), (163863/16384000000000), (1474767/32768000000000), (491589/4096000000000), (3441123/16384000000000), (10323369/40960000000000), (3441123/16384000000000), (495189/4096000000000), (1564687/32768000000000), (210801/16384000000000), (163863/81920000000000)]

theorem checked0263 :
    (∀ i, 0 ≤ plusWeights0263 i) ∧
    (∀ i, 0 ≤ minusWeights0263 i) ∧
    (∀ i, plusCoefficients coefficients0263 upper0263 i = powerCoefficients10 plusWeights0263 i) ∧
    (∀ i, minusCoefficients coefficients0263 upper0263 i = powerCoefficients10 minusWeights0263 i) := by
  decide +kernel

theorem bound0263 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0263 g| ≤ (upper0263 : ℝ) :=
  abs_of_coefficients coefficients0263 upper0263 powerCoefficients10 plusWeights0263 minusWeights0263
    checked0263.1 checked0263.2.1 checked0263.2.2.1 checked0263.2.2.2
    (power_identity10 plusWeights0263) (power_identity10 minusWeights0263) g hg hmax

def envelope0263 : Envelope := ⟨coefficients0263, upper0263, bound0263⟩

def coefficients0264 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/2048), (-15/2048), (-605/16384), (-575/32768)]

def upper0264 : ℚ := (11067/13107200000000)

def plusWeights0264 : Fin 11 → ℚ := ![(11067/13107200000000), (11067/1310720000000), (99603/2621440000000), (33201/327680000000), (232407/1310720000000), (697221/3276800000000), (232407/1310720000000), (32961/327680000000), (93651/2621440000000), (39733/6553600000000), 0]

def minusWeights0264 : Fin 11 → ℚ := ![(11067/13107200000000), (11067/1310720000000), (99603/2621440000000), (33201/327680000000), (232407/1310720000000), (697221/3276800000000), (232407/1310720000000), (33441/327680000000), (21111/524288000000), (70937/6553600000000), (11067/6553600000000)]

theorem checked0264 :
    (∀ i, 0 ≤ plusWeights0264 i) ∧
    (∀ i, 0 ≤ minusWeights0264 i) ∧
    (∀ i, plusCoefficients coefficients0264 upper0264 i = powerCoefficients10 plusWeights0264 i) ∧
    (∀ i, minusCoefficients coefficients0264 upper0264 i = powerCoefficients10 minusWeights0264 i) := by
  decide +kernel

theorem bound0264 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0264 g| ≤ (upper0264 : ℝ) :=
  abs_of_coefficients coefficients0264 upper0264 powerCoefficients10 plusWeights0264 minusWeights0264
    checked0264.1 checked0264.2.1 checked0264.2.2.1 checked0264.2.2.2
    (power_identity10 plusWeights0264) (power_identity10 minusWeights0264) g hg hmax

def envelope0264 : Envelope := ⟨coefficients0264, upper0264, bound0264⟩

def coefficients0265 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/2048), (-15/2048), (-165/8192), (-75/8192)]

def upper0265 : ℚ := (2709/3276800000000)

def plusWeights0265 : Fin 11 → ℚ := ![(2709/3276800000000), (2709/327680000000), (24381/655360000000), (8127/81920000000), (56889/327680000000), (170667/819200000000), (56889/327680000000), (8067/81920000000), (22893/655360000000), (1209/204800000000), 0]

def minusWeights0265 : Fin 11 → ℚ := ![(2709/3276800000000), (2709/327680000000), (24381/655360000000), (8127/81920000000), (56889/327680000000), (170667/819200000000), (56889/327680000000), (8187/81920000000), (25869/655360000000), (8709/819200000000), (2709/1638400000000)]

theorem checked0265 :
    (∀ i, 0 ≤ plusWeights0265 i) ∧
    (∀ i, 0 ≤ minusWeights0265 i) ∧
    (∀ i, plusCoefficients coefficients0265 upper0265 i = powerCoefficients10 plusWeights0265 i) ∧
    (∀ i, minusCoefficients coefficients0265 upper0265 i = powerCoefficients10 minusWeights0265 i) := by
  decide +kernel

theorem bound0265 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0265 g| ≤ (upper0265 : ℝ) :=
  abs_of_coefficients coefficients0265 upper0265 powerCoefficients10 plusWeights0265 minusWeights0265
    checked0265.1 checked0265.2.1 checked0265.2.2.1 checked0265.2.2.2
    (power_identity10 plusWeights0265) (power_identity10 minusWeights0265) g hg hmax

def envelope0265 : Envelope := ⟨coefficients0265, upper0265, bound0265⟩

def coefficients0266 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/2048), (-15/2048), (-485/32768), (-425/65536)]

def upper0266 : ℚ := (861/1048576000000)

def plusWeights0266 : Fin 11 → ℚ := ![(861/1048576000000), (861/104857600000), (7749/209715200000), (2583/26214400000), (18081/104857600000), (54243/262144000000), (18081/104857600000), (12819/131072000000), (181821/5242880000000), (76711/13107200000000), 0]

def minusWeights0266 : Fin 11 → ℚ := ![(861/1048576000000), (861/104857600000), (7749/209715200000), (2583/26214400000), (18081/104857600000), (54243/262144000000), (18081/104857600000), (13011/131072000000), (205629/5242880000000), (138539/13107200000000), (861/524288000000)]

theorem checked0266 :
    (∀ i, 0 ≤ plusWeights0266 i) ∧
    (∀ i, 0 ≤ minusWeights0266 i) ∧
    (∀ i, plusCoefficients coefficients0266 upper0266 i = powerCoefficients10 plusWeights0266 i) ∧
    (∀ i, minusCoefficients coefficients0266 upper0266 i = powerCoefficients10 minusWeights0266 i) := by
  decide +kernel

theorem bound0266 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0266 g| ≤ (upper0266 : ℝ) :=
  abs_of_coefficients coefficients0266 upper0266 powerCoefficients10 plusWeights0266 minusWeights0266
    checked0266.1 checked0266.2.1 checked0266.2.2.1 checked0266.2.2.2
    (power_identity10 plusWeights0266) (power_identity10 minusWeights0266) g hg hmax

def envelope0266 : Envelope := ⟨coefficients0266, upper0266, bound0266⟩

def coefficients0267 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/2048), (-15/2048), (-105/16384), (-75/32768)]

def upper0267 : ℚ := (10647/13107200000000)

def plusWeights0267 : Fin 11 → ℚ := ![(10647/13107200000000), (10647/1310720000000), (95823/2621440000000), (31941/327680000000), (223587/1310720000000), (670761/3276800000000), (223587/1310720000000), (31701/327680000000), (89871/2621440000000), (37833/6553600000000), 0]

def minusWeights0267 : Fin 11 → ℚ := ![(10647/13107200000000), (10647/1310720000000), (95823/2621440000000), (31941/327680000000), (223587/1310720000000), (670761/3276800000000), (223587/1310720000000), (32181/327680000000), (4071/104857600000), (68637/6553600000000), (10647/6553600000000)]

theorem checked0267 :
    (∀ i, 0 ≤ plusWeights0267 i) ∧
    (∀ i, 0 ≤ minusWeights0267 i) ∧
    (∀ i, plusCoefficients coefficients0267 upper0267 i = powerCoefficients10 plusWeights0267 i) ∧
    (∀ i, minusCoefficients coefficients0267 upper0267 i = powerCoefficients10 minusWeights0267 i) := by
  decide +kernel

theorem bound0267 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0267 g| ≤ (upper0267 : ℝ) :=
  abs_of_coefficients coefficients0267 upper0267 powerCoefficients10 plusWeights0267 minusWeights0267
    checked0267.1 checked0267.2.1 checked0267.2.2.1 checked0267.2.2.2
    (power_identity10 plusWeights0267) (power_identity10 minusWeights0267) g hg hmax

def envelope0267 : Envelope := ⟨coefficients0267, upper0267, bound0267⟩

def coefficients0268 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-25/4096), (75/16384), (75/32768), (375/262144)]

def upper0268 : ℚ := (11789/20971520000000)

def plusWeights0268 : Fin 11 → ℚ := ![(11789/20971520000000), (11789/2097152000000), (106101/4194304000000), (35367/524288000000), (247569/2097152000000), (742707/5242880000000), (247569/2097152000000), (35047/524288000000), (98613/4194304000000), (40729/10485760000000), 0]

def minusWeights0268 : Fin 11 → ℚ := ![(11789/20971520000000), (11789/2097152000000), (106101/4194304000000), (35367/524288000000), (247569/2097152000000), (742707/5242880000000), (247569/2097152000000), (35687/524288000000), (113589/4194304000000), (77161/10485760000000), (11789/10485760000000)]

theorem checked0268 :
    (∀ i, 0 ≤ plusWeights0268 i) ∧
    (∀ i, 0 ≤ minusWeights0268 i) ∧
    (∀ i, plusCoefficients coefficients0268 upper0268 i = powerCoefficients10 plusWeights0268 i) ∧
    (∀ i, minusCoefficients coefficients0268 upper0268 i = powerCoefficients10 minusWeights0268 i) := by
  decide +kernel

theorem bound0268 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0268 g| ≤ (upper0268 : ℝ) :=
  abs_of_coefficients coefficients0268 upper0268 powerCoefficients10 plusWeights0268 minusWeights0268
    checked0268.1 checked0268.2.1 checked0268.2.2.1 checked0268.2.2.2
    (power_identity10 plusWeights0268) (power_identity10 minusWeights0268) g hg hmax

def envelope0268 : Envelope := ⟨coefficients0268, upper0268, bound0268⟩

def coefficients0269 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-25/4096), (175/16384), (175/32768), (875/131072)]

def upper0269 : ℚ := (5217/10485760000000)

def plusWeights0269 : Fin 11 → ℚ := ![(5217/10485760000000), (5217/1048576000000), (46953/2097152000000), (15651/262144000000), (109557/1048576000000), (328671/2621440000000), (109557/1048576000000), (15491/262144000000), (43337/2097152000000), (17633/5242880000000), 0]

def minusWeights0269 : Fin 11 → ℚ := ![(5217/10485760000000), (5217/1048576000000), (46953/2097152000000), (15651/262144000000), (109557/1048576000000), (328671/2621440000000), (109557/1048576000000), (15811/262144000000), (50569/2097152000000), (34537/5242880000000), (5217/5242880000000)]

theorem checked0269 :
    (∀ i, 0 ≤ plusWeights0269 i) ∧
    (∀ i, 0 ≤ minusWeights0269 i) ∧
    (∀ i, plusCoefficients coefficients0269 upper0269 i = powerCoefficients10 plusWeights0269 i) ∧
    (∀ i, minusCoefficients coefficients0269 upper0269 i = powerCoefficients10 minusWeights0269 i) := by
  decide +kernel

theorem bound0269 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0269 g| ≤ (upper0269 : ℝ) :=
  abs_of_coefficients coefficients0269 upper0269 powerCoefficients10 plusWeights0269 minusWeights0269
    checked0269.1 checked0269.2.1 checked0269.2.2.1 checked0269.2.2.2
    (power_identity10 plusWeights0269) (power_identity10 minusWeights0269) g hg hmax

def envelope0269 : Envelope := ⟨coefficients0269, upper0269, bound0269⟩

def coefficients0270 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-45/8192), (15/4096), (-105/8192), (-225/32768)]

def upper0270 : ℚ := (6897/13107200000000)

def plusWeights0270 : Fin 11 → ℚ := ![(6897/13107200000000), (6897/1310720000000), (62073/2621440000000), (20691/327680000000), (144837/1310720000000), (434511/3276800000000), (144837/1310720000000), (20511/327680000000), (57849/2621440000000), (24081/6553600000000), 0]

def minusWeights0270 : Fin 11 → ℚ := ![(6897/13107200000000), (6897/1310720000000), (62073/2621440000000), (20691/327680000000), (144837/1310720000000), (434511/3276800000000), (144837/1310720000000), (20871/327680000000), (66297/2621440000000), (44889/6553600000000), (6897/6553600000000)]

theorem checked0270 :
    (∀ i, 0 ≤ plusWeights0270 i) ∧
    (∀ i, 0 ≤ minusWeights0270 i) ∧
    (∀ i, plusCoefficients coefficients0270 upper0270 i = powerCoefficients10 plusWeights0270 i) ∧
    (∀ i, minusCoefficients coefficients0270 upper0270 i = powerCoefficients10 minusWeights0270 i) := by
  decide +kernel

theorem bound0270 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0270 g| ≤ (upper0270 : ℝ) :=
  abs_of_coefficients coefficients0270 upper0270 powerCoefficients10 plusWeights0270 minusWeights0270
    checked0270.1 checked0270.2.1 checked0270.2.2.1 checked0270.2.2.2
    (power_identity10 plusWeights0270) (power_identity10 minusWeights0270) g hg hmax

def envelope0270 : Envelope := ⟨coefficients0270, upper0270, bound0270⟩

def coefficients0271 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/1024), (-5/1024), (-185/8192), (-175/16384)]

def upper0271 : ℚ := (147/262144000000)

def plusWeights0271 : Fin 11 → ℚ := ![(147/262144000000), (147/26214400000), (1323/52428800000), (441/6553600000), (3087/26214400000), (9261/65536000000), (3087/26214400000), (2189/32768000000), (31091/1310720000000), (13181/3276800000000), 0]

def minusWeights0271 : Fin 11 → ℚ := ![(147/262144000000), (147/26214400000), (1323/52428800000), (441/6553600000), (3087/26214400000), (9261/65536000000), (3087/26214400000), (2221/32768000000), (35059/1310720000000), (23569/3276800000000), (147/131072000000)]

theorem checked0271 :
    (∀ i, 0 ≤ plusWeights0271 i) ∧
    (∀ i, 0 ≤ minusWeights0271 i) ∧
    (∀ i, plusCoefficients coefficients0271 upper0271 i = powerCoefficients10 plusWeights0271 i) ∧
    (∀ i, minusCoefficients coefficients0271 upper0271 i = powerCoefficients10 minusWeights0271 i) := by
  decide +kernel

theorem bound0271 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0271 g| ≤ (upper0271 : ℝ) :=
  abs_of_coefficients coefficients0271 upper0271 powerCoefficients10 plusWeights0271 minusWeights0271
    checked0271.1 checked0271.2.1 checked0271.2.2.1 checked0271.2.2.2
    (power_identity10 plusWeights0271) (power_identity10 minusWeights0271) g hg hmax

def envelope0271 : Envelope := ⟨coefficients0271, upper0271, bound0271⟩

def coefficients0272 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/1024), (-5/1024), (-465/32768), (-425/65536)]

def upper0272 : ℚ := (14469/26214400000000)

def plusWeights0272 : Fin 11 → ℚ := ![(14469/26214400000000), (14469/2621440000000), (130221/5242880000000), (43407/655360000000), (303849/2621440000000), (911547/6553600000000), (303849/2621440000000), (43087/655360000000), (24457/1048576000000), (51679/13107200000000), 0]

def minusWeights0272 : Fin 11 → ℚ := ![(14469/26214400000000), (14469/2621440000000), (130221/5242880000000), (43407/655360000000), (303849/2621440000000), (911547/6553600000000), (303849/2621440000000), (43727/655360000000), (138157/5242880000000), (93011/13107200000000), (14469/13107200000000)]

theorem checked0272 :
    (∀ i, 0 ≤ plusWeights0272 i) ∧
    (∀ i, 0 ≤ minusWeights0272 i) ∧
    (∀ i, plusCoefficients coefficients0272 upper0272 i = powerCoefficients10 plusWeights0272 i) ∧
    (∀ i, minusCoefficients coefficients0272 upper0272 i = powerCoefficients10 minusWeights0272 i) := by
  decide +kernel

theorem bound0272 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0272 g| ≤ (upper0272 : ℝ) :=
  abs_of_coefficients coefficients0272 upper0272 powerCoefficients10 plusWeights0272 minusWeights0272
    checked0272.1 checked0272.2.1 checked0272.2.2.1 checked0272.2.2.2
    (power_identity10 plusWeights0272) (power_identity10 minusWeights0272) g hg hmax

def envelope0272 : Envelope := ⟨coefficients0272, upper0272, bound0272⟩

def coefficients0273 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/1024), (-5/1024), (-55/4096), (-25/4096)]

def upper0273 : ℚ := (903/1638400000000)

def plusWeights0273 : Fin 11 → ℚ := ![(903/1638400000000), (903/163840000000), (8127/327680000000), (2709/40960000000), (18963/163840000000), (56889/409600000000), (18963/163840000000), (2689/40960000000), (7631/327680000000), (403/102400000000), 0]

def minusWeights0273 : Fin 11 → ℚ := ![(903/1638400000000), (903/163840000000), (8127/327680000000), (2709/40960000000), (18963/163840000000), (56889/409600000000), (18963/163840000000), (2729/40960000000), (8623/327680000000), (2903/409600000000), (903/819200000000)]

theorem checked0273 :
    (∀ i, 0 ≤ plusWeights0273 i) ∧
    (∀ i, 0 ≤ minusWeights0273 i) ∧
    (∀ i, plusCoefficients coefficients0273 upper0273 i = powerCoefficients10 plusWeights0273 i) ∧
    (∀ i, minusCoefficients coefficients0273 upper0273 i = powerCoefficients10 minusWeights0273 i) := by
  decide +kernel

theorem bound0273 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0273 g| ≤ (upper0273 : ℝ) :=
  abs_of_coefficients coefficients0273 upper0273 powerCoefficients10 plusWeights0273 minusWeights0273
    checked0273.1 checked0273.2.1 checked0273.2.2.1 checked0273.2.2.2
    (power_identity10 plusWeights0273) (power_identity10 minusWeights0273) g hg hmax

def envelope0273 : Envelope := ⟨coefficients0273, upper0273, bound0273⟩

def coefficients0274 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/1024), (-5/1024), (-195/16384), (-175/32768)]

def upper0274 : ℚ := (7203/13107200000000)

def plusWeights0274 : Fin 11 → ℚ := ![(7203/13107200000000), (7203/1310720000000), (64827/2621440000000), (21609/327680000000), (151263/1310720000000), (453789/3276800000000), (151263/1310720000000), (21449/327680000000), (60859/2621440000000), (25697/6553600000000), 0]

def minusWeights0274 : Fin 11 → ℚ := ![(7203/13107200000000), (7203/1310720000000), (64827/2621440000000), (21609/327680000000), (151263/1310720000000), (453789/3276800000000), (151263/1310720000000), (21769/327680000000), (13759/524288000000), (46333/6553600000000), (7203/6553600000000)]

theorem checked0274 :
    (∀ i, 0 ≤ plusWeights0274 i) ∧
    (∀ i, 0 ≤ minusWeights0274 i) ∧
    (∀ i, plusCoefficients coefficients0274 upper0274 i = powerCoefficients10 plusWeights0274 i) ∧
    (∀ i, minusCoefficients coefficients0274 upper0274 i = powerCoefficients10 minusWeights0274 i) := by
  decide +kernel

theorem bound0274 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0274 g| ≤ (upper0274 : ℝ) :=
  abs_of_coefficients coefficients0274 upper0274 powerCoefficients10 plusWeights0274 minusWeights0274
    checked0274.1 checked0274.2.1 checked0274.2.2.1 checked0274.2.2.2
    (power_identity10 plusWeights0274) (power_identity10 minusWeights0274) g hg hmax

def envelope0274 : Envelope := ⟨coefficients0274, upper0274, bound0274⟩

def coefficients0275 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/1024), (-5/1024), (-145/16384), (-125/32768)]

def upper0275 : ℚ := (7161/13107200000000)

def plusWeights0275 : Fin 11 → ℚ := ![(7161/13107200000000), (7161/1310720000000), (64449/2621440000000), (21483/327680000000), (150381/1310720000000), (451143/3276800000000), (150381/1310720000000), (21323/327680000000), (60481/2621440000000), (25507/6553600000000), 0]

def minusWeights0275 : Fin 11 → ℚ := ![(7161/13107200000000), (7161/1310720000000), (64449/2621440000000), (21483/327680000000), (150381/1310720000000), (451143/3276800000000), (150381/1310720000000), (21643/327680000000), (68417/2621440000000), (46103/6553600000000), (7161/6553600000000)]

theorem checked0275 :
    (∀ i, 0 ≤ plusWeights0275 i) ∧
    (∀ i, 0 ≤ minusWeights0275 i) ∧
    (∀ i, plusCoefficients coefficients0275 upper0275 i = powerCoefficients10 plusWeights0275 i) ∧
    (∀ i, minusCoefficients coefficients0275 upper0275 i = powerCoefficients10 minusWeights0275 i) := by
  decide +kernel

theorem bound0275 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0275 g| ≤ (upper0275 : ℝ) :=
  abs_of_coefficients coefficients0275 upper0275 powerCoefficients10 plusWeights0275 minusWeights0275
    checked0275.1 checked0275.2.1 checked0275.2.2.1 checked0275.2.2.2
    (power_identity10 plusWeights0275) (power_identity10 minusWeights0275) g hg hmax

def envelope0275 : Envelope := ⟨coefficients0275, upper0275, bound0275⟩

def coefficients0276 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/1024), (-5/1024), (-35/8192), (-25/16384)]

def upper0276 : ℚ := (3549/6553600000000)

def plusWeights0276 : Fin 11 → ℚ := ![(3549/6553600000000), (3549/655360000000), (31941/1310720000000), (10647/163840000000), (74529/655360000000), (223587/1638400000000), (74529/655360000000), (10567/163840000000), (29957/1310720000000), (12611/3276800000000), 0]

def minusWeights0276 : Fin 11 → ℚ := ![(3549/6553600000000), (3549/655360000000), (31941/1310720000000), (10647/163840000000), (74529/655360000000), (223587/1638400000000), (74529/655360000000), (10727/163840000000), (1357/52428800000), (22879/3276800000000), (3549/3276800000000)]

theorem checked0276 :
    (∀ i, 0 ≤ plusWeights0276 i) ∧
    (∀ i, 0 ≤ minusWeights0276 i) ∧
    (∀ i, plusCoefficients coefficients0276 upper0276 i = powerCoefficients10 plusWeights0276 i) ∧
    (∀ i, minusCoefficients coefficients0276 upper0276 i = powerCoefficients10 minusWeights0276 i) := by
  decide +kernel

theorem bound0276 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0276 g| ≤ (upper0276 : ℝ) :=
  abs_of_coefficients coefficients0276 upper0276 powerCoefficients10 plusWeights0276 minusWeights0276
    checked0276.1 checked0276.2.1 checked0276.2.2.1 checked0276.2.2.2
    (power_identity10 plusWeights0276) (power_identity10 minusWeights0276) g hg hmax

def envelope0276 : Envelope := ⟨coefficients0276, upper0276, bound0276⟩

def coefficients0277 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/1024), (-5/1024), (-45/16384), (-25/32768)]

def upper0277 : ℚ := (7077/13107200000000)

def plusWeights0277 : Fin 11 → ℚ := ![(7077/13107200000000), (7077/1310720000000), (63693/2621440000000), (21231/327680000000), (148617/1310720000000), (445851/3276800000000), (148617/1310720000000), (21071/327680000000), (2389/104857600000), (25127/6553600000000), 0]

def minusWeights0277 : Fin 11 → ℚ := ![(7077/13107200000000), (7077/1310720000000), (63693/2621440000000), (21231/327680000000), (148617/1310720000000), (445851/3276800000000), (148617/1310720000000), (21391/327680000000), (67661/2621440000000), (45643/6553600000000), (7077/6553600000000)]

theorem checked0277 :
    (∀ i, 0 ≤ plusWeights0277 i) ∧
    (∀ i, 0 ≤ minusWeights0277 i) ∧
    (∀ i, plusCoefficients coefficients0277 upper0277 i = powerCoefficients10 plusWeights0277 i) ∧
    (∀ i, minusCoefficients coefficients0277 upper0277 i = powerCoefficients10 minusWeights0277 i) := by
  decide +kernel

theorem bound0277 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0277 g| ≤ (upper0277 : ℝ) :=
  abs_of_coefficients coefficients0277 upper0277 powerCoefficients10 plusWeights0277 minusWeights0277
    checked0277.1 checked0277.2.1 checked0277.2.2.1 checked0277.2.2.2
    (power_identity10 plusWeights0277) (power_identity10 minusWeights0277) g hg hmax

def envelope0277 : Envelope := ⟨coefficients0277, upper0277, bound0277⟩

def coefficients0278 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/2048), (-11/2048), (-693/32768), (-641/65536)]

def upper0278 : ℚ := (337701/655360000000000)

def plusWeights0278 : Fin 11 → ℚ := ![(337701/655360000000000), (337701/65536000000000), (3039309/131072000000000), (1013103/16384000000000), (7091721/65536000000000), (21275163/163840000000000), (7091721/65536000000000), (1005903/16384000000000), (2859469/131072000000000), (1943/524288000000), 0]

def minusWeights0278 : Fin 11 → ℚ := ![(337701/655360000000000), (337701/65536000000000), (3039309/131072000000000), (1013103/16384000000000), (7091721/65536000000000), (21275163/163840000000000), (7091721/65536000000000), (1020303/16384000000000), (3219149/131072000000000), (432527/65536000000000), (337701/327680000000000)]

theorem checked0278 :
    (∀ i, 0 ≤ plusWeights0278 i) ∧
    (∀ i, 0 ≤ minusWeights0278 i) ∧
    (∀ i, plusCoefficients coefficients0278 upper0278 i = powerCoefficients10 plusWeights0278 i) ∧
    (∀ i, minusCoefficients coefficients0278 upper0278 i = powerCoefficients10 minusWeights0278 i) := by
  decide +kernel

theorem bound0278 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0278 g| ≤ (upper0278 : ℝ) :=
  abs_of_coefficients coefficients0278 upper0278 powerCoefficients10 plusWeights0278 minusWeights0278
    checked0278.1 checked0278.2.1 checked0278.2.2.1 checked0278.2.2.2
    (power_identity10 plusWeights0278) (power_identity10 minusWeights0278) g hg hmax

def envelope0278 : Envelope := ⟨coefficients0278, upper0278, bound0278⟩

def coefficients0279 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/2048), (-11/2048), (-643/32768), (-591/65536)]

def upper0279 : ℚ := (336651/655360000000000)

def plusWeights0279 : Fin 11 → ℚ := ![(336651/655360000000000), (336651/65536000000000), (3029859/131072000000000), (1009953/16384000000000), (7069671/65536000000000), (21209013/163840000000000), (7069671/65536000000000), (1002753/16384000000000), (2850019/131072000000000), (9677/2621440000000), 0]

def minusWeights0279 : Fin 11 → ℚ := ![(336651/655360000000000), (336651/65536000000000), (3029859/131072000000000), (1009953/16384000000000), (7069671/65536000000000), (21209013/163840000000000), (7069671/65536000000000), (1017153/16384000000000), (3209699/131072000000000), (431377/65536000000000), (336651/327680000000000)]

theorem checked0279 :
    (∀ i, 0 ≤ plusWeights0279 i) ∧
    (∀ i, 0 ≤ minusWeights0279 i) ∧
    (∀ i, plusCoefficients coefficients0279 upper0279 i = powerCoefficients10 plusWeights0279 i) ∧
    (∀ i, minusCoefficients coefficients0279 upper0279 i = powerCoefficients10 minusWeights0279 i) := by
  decide +kernel

theorem bound0279 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0279 g| ≤ (upper0279 : ℝ) :=
  abs_of_coefficients coefficients0279 upper0279 powerCoefficients10 plusWeights0279 minusWeights0279
    checked0279.1 checked0279.2.1 checked0279.2.2.1 checked0279.2.2.2
    (power_identity10 plusWeights0279) (power_identity10 minusWeights0279) g hg hmax

def envelope0279 : Envelope := ⟨coefficients0279, upper0279, bound0279⟩

def coefficients0280 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/2048), (-11/2048), (-209/16384), (-183/32768)]

def upper0280 : ℚ := (165963/327680000000000)

def plusWeights0280 : Fin 11 → ℚ := ![(165963/327680000000000), (165963/32768000000000), (1493667/65536000000000), (497889/8192000000000), (3485223/32768000000000), (10455669/81920000000000), (3485223/32768000000000), (494289/8192000000000), (1403747/65536000000000), (4753/1310720000000), 0]

def minusWeights0280 : Fin 11 → ℚ := ![(165963/327680000000000), (165963/32768000000000), (1493667/65536000000000), (497889/8192000000000), (3485223/32768000000000), (10455669/81920000000000), (3485223/32768000000000), (501489/8192000000000), (1583587/65536000000000), (213101/32768000000000), (165963/163840000000000)]

theorem checked0280 :
    (∀ i, 0 ≤ plusWeights0280 i) ∧
    (∀ i, 0 ≤ minusWeights0280 i) ∧
    (∀ i, plusCoefficients coefficients0280 upper0280 i = powerCoefficients10 plusWeights0280 i) ∧
    (∀ i, minusCoefficients coefficients0280 upper0280 i = powerCoefficients10 minusWeights0280 i) := by
  decide +kernel

theorem bound0280 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0280 g| ≤ (upper0280 : ℝ) :=
  abs_of_coefficients coefficients0280 upper0280 powerCoefficients10 plusWeights0280 minusWeights0280
    checked0280.1 checked0280.2.1 checked0280.2.2.1 checked0280.2.2.2
    (power_identity10 plusWeights0280) (power_identity10 minusWeights0280) g hg hmax

def envelope0280 : Envelope := ⟨coefficients0280, upper0280, bound0280⟩

def coefficients0281 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-35/8192), (-5/4096), (-5/1024), (-75/32768)]

def upper0281 : ℚ := (5827/13107200000000)

def plusWeights0281 : Fin 11 → ℚ := ![(5827/13107200000000), (5827/1310720000000), (52443/2621440000000), (17481/327680000000), (122367/1310720000000), (367101/3276800000000), (122367/1310720000000), (17341/327680000000), (49051/2621440000000), (20543/6553600000000), 0]

def minusWeights0281 : Fin 11 → ℚ := ![(5827/13107200000000), (5827/1310720000000), (52443/2621440000000), (17481/327680000000), (122367/1310720000000), (367101/3276800000000), (122367/1310720000000), (17621/327680000000), (11167/524288000000), (37727/6553600000000), (5827/6553600000000)]

theorem checked0281 :
    (∀ i, 0 ≤ plusWeights0281 i) ∧
    (∀ i, 0 ≤ minusWeights0281 i) ∧
    (∀ i, plusCoefficients coefficients0281 upper0281 i = powerCoefficients10 plusWeights0281 i) ∧
    (∀ i, minusCoefficients coefficients0281 upper0281 i = powerCoefficients10 minusWeights0281 i) := by
  decide +kernel

theorem bound0281 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0281 g| ≤ (upper0281 : ℝ) :=
  abs_of_coefficients coefficients0281 upper0281 powerCoefficients10 plusWeights0281 minusWeights0281
    checked0281.1 checked0281.2.1 checked0281.2.2.1 checked0281.2.2.2
    (power_identity10 plusWeights0281) (power_identity10 minusWeights0281) g hg hmax

def envelope0281 : Envelope := ⟨coefficients0281, upper0281, bound0281⟩

def coefficients0282 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/4096), (15/1024), (-105/32768), (-225/65536)]

def upper0282 : ℚ := (5853/26214400000000)

def plusWeights0282 : Fin 11 → ℚ := ![(5853/26214400000000), (5853/2621440000000), (52677/5242880000000), (17559/655360000000), (122913/2621440000000), (368739/6553600000000), (122913/2621440000000), (17319/655360000000), (9537/1048576000000), (18663/13107200000000), 0]

def minusWeights0282 : Fin 11 → ℚ := ![(5853/26214400000000), (5853/2621440000000), (52677/5242880000000), (17559/655360000000), (122913/2621440000000), (368739/6553600000000), (122913/2621440000000), (17799/655360000000), (57669/5242880000000), (39867/13107200000000), (5853/13107200000000)]

theorem checked0282 :
    (∀ i, 0 ≤ plusWeights0282 i) ∧
    (∀ i, 0 ≤ minusWeights0282 i) ∧
    (∀ i, plusCoefficients coefficients0282 upper0282 i = powerCoefficients10 plusWeights0282 i) ∧
    (∀ i, minusCoefficients coefficients0282 upper0282 i = powerCoefficients10 minusWeights0282 i) := by
  decide +kernel

theorem bound0282 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0282 g| ≤ (upper0282 : ℝ) :=
  abs_of_coefficients coefficients0282 upper0282 powerCoefficients10 plusWeights0282 minusWeights0282
    checked0282.1 checked0282.2.1 checked0282.2.2.1 checked0282.2.2.2
    (power_identity10 plusWeights0282) (power_identity10 minusWeights0282) g hg hmax

def envelope0282 : Envelope := ⟨coefficients0282, upper0282, bound0282⟩

def coefficients0283 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-25/8192), (175/32768), (175/65536), (2375/262144)]

def upper0283 : ℚ := (1041/4194304000000)

def plusWeights0283 : Fin 11 → ℚ := ![(1041/4194304000000), (1041/419430400000), (9369/838860800000), (3123/104857600000), (21861/419430400000), (65583/1048576000000), (21861/419430400000), (3091/104857600000), (43229/4194304000000), (17573/10485760000000), 0]

def minusWeights0283 : Fin 11 → ℚ := ![(1041/4194304000000), (1041/419430400000), (9369/838860800000), (3123/104857600000), (21861/419430400000), (65583/1048576000000), (21861/419430400000), (631/20971520000), (50461/4194304000000), (34477/10485760000000), (1041/2097152000000)]

theorem checked0283 :
    (∀ i, 0 ≤ plusWeights0283 i) ∧
    (∀ i, 0 ≤ minusWeights0283 i) ∧
    (∀ i, plusCoefficients coefficients0283 upper0283 i = powerCoefficients10 plusWeights0283 i) ∧
    (∀ i, minusCoefficients coefficients0283 upper0283 i = powerCoefficients10 minusWeights0283 i) := by
  decide +kernel

theorem bound0283 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0283 g| ≤ (upper0283 : ℝ) :=
  abs_of_coefficients coefficients0283 upper0283 powerCoefficients10 plusWeights0283 minusWeights0283
    checked0283.1 checked0283.2.1 checked0283.2.2.1 checked0283.2.2.2
    (power_identity10 plusWeights0283) (power_identity10 minusWeights0283) g hg hmax

def envelope0283 : Envelope := ⟨coefficients0283, upper0283, bound0283⟩

def coefficients0284 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-23/8192), (-1/4096), (-353/65536), (-341/131072)]

def upper0284 : ℚ := (378601/1310720000000000)

def plusWeights0284 : Fin 11 → ℚ := ![(378601/1310720000000000), (378601/131072000000000), (3407409/262144000000000), (1135803/32768000000000), (7950621/131072000000000), (23851863/327680000000000), (7950621/131072000000000), (1126603/32768000000000), (3185969/262144000000000), (53371/26214400000000), 0]

def minusWeights0284 : Fin 11 → ℚ := ![(378601/1310720000000000), (378601/131072000000000), (3407409/262144000000000), (1135803/32768000000000), (7950621/131072000000000), (23851863/327680000000000), (7950621/131072000000000), (1145003/32768000000000), (3628849/262144000000000), (490347/131072000000000), (378601/655360000000000)]

theorem checked0284 :
    (∀ i, 0 ≤ plusWeights0284 i) ∧
    (∀ i, 0 ≤ minusWeights0284 i) ∧
    (∀ i, plusCoefficients coefficients0284 upper0284 i = powerCoefficients10 plusWeights0284 i) ∧
    (∀ i, minusCoefficients coefficients0284 upper0284 i = powerCoefficients10 minusWeights0284 i) := by
  decide +kernel

theorem bound0284 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0284 g| ≤ (upper0284 : ℝ) :=
  abs_of_coefficients coefficients0284 upper0284 powerCoefficients10 plusWeights0284 minusWeights0284
    checked0284.1 checked0284.2.1 checked0284.2.2.1 checked0284.2.2.2
    (power_identity10 plusWeights0284) (power_identity10 minusWeights0284) g hg hmax

def envelope0284 : Envelope := ⟨coefficients0284, upper0284, bound0284⟩

def coefficients0285 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/2048), (-5/2048), (-85/16384), (-75/32768)]

def upper0285 : ℚ := (3591/13107200000000)

def plusWeights0285 : Fin 11 → ℚ := ![(3591/13107200000000), (3591/1310720000000), (32319/2621440000000), (10773/327680000000), (75411/1310720000000), (226233/3276800000000), (75411/1310720000000), (10693/327680000000), (6067/524288000000), (12801/6553600000000), 0]

def minusWeights0285 : Fin 11 → ℚ := ![(3591/13107200000000), (3591/1310720000000), (32319/2621440000000), (10773/327680000000), (75411/1310720000000), (226233/3276800000000), (75411/1310720000000), (10853/327680000000), (34303/2621440000000), (23109/6553600000000), (3591/6553600000000)]

theorem checked0285 :
    (∀ i, 0 ≤ plusWeights0285 i) ∧
    (∀ i, 0 ≤ minusWeights0285 i) ∧
    (∀ i, plusCoefficients coefficients0285 upper0285 i = powerCoefficients10 plusWeights0285 i) ∧
    (∀ i, minusCoefficients coefficients0285 upper0285 i = powerCoefficients10 minusWeights0285 i) := by
  decide +kernel

theorem bound0285 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0285 g| ≤ (upper0285 : ℝ) :=
  abs_of_coefficients coefficients0285 upper0285 powerCoefficients10 plusWeights0285 minusWeights0285
    checked0285.1 checked0285.2.1 checked0285.2.2.1 checked0285.2.2.2
    (power_identity10 plusWeights0285) (power_identity10 minusWeights0285) g hg hmax

def envelope0285 : Envelope := ⟨coefficients0285, upper0285, bound0285⟩

def coefficients0286 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-225/8192), (-225/16384), (3375/131072)]

def upper0286 : ℚ := (2997/10485760000000)

def plusWeights0286 : Fin 11 → ℚ := ![(2997/10485760000000), (2997/1048576000000), (26973/2097152000000), (8991/262144000000), (62937/1048576000000), (188811/2621440000000), (62937/1048576000000), (8991/262144000000), (26397/2097152000000), (12033/5242880000000), 0]

def minusWeights0286 : Fin 11 → ℚ := ![(2997/10485760000000), (2997/1048576000000), (26973/2097152000000), (8991/262144000000), (62937/1048576000000), (188811/2621440000000), (62937/1048576000000), (8991/262144000000), (27549/2097152000000), (17937/5242880000000), (2997/5242880000000)]

theorem checked0286 :
    (∀ i, 0 ≤ plusWeights0286 i) ∧
    (∀ i, 0 ≤ minusWeights0286 i) ∧
    (∀ i, plusCoefficients coefficients0286 upper0286 i = powerCoefficients10 plusWeights0286 i) ∧
    (∀ i, minusCoefficients coefficients0286 upper0286 i = powerCoefficients10 minusWeights0286 i) := by
  decide +kernel

theorem bound0286 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0286 g| ≤ (upper0286 : ℝ) :=
  abs_of_coefficients coefficients0286 upper0286 powerCoefficients10 plusWeights0286 minusWeights0286
    checked0286.1 checked0286.2.1 checked0286.2.2.1 checked0286.2.2.2
    (power_identity10 plusWeights0286) (power_identity10 minusWeights0286) g hg hmax

def envelope0286 : Envelope := ⟨coefficients0286, upper0286, bound0286⟩

def coefficients0287 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-375/16384), (-375/32768), (-1875/262144)]

def upper0287 : ℚ := (1011/4194304000000)

def plusWeights0287 : Fin 11 → ℚ := ![(1011/4194304000000), (1011/419430400000), (9099/838860800000), (3033/104857600000), (21231/419430400000), (63693/1048576000000), (21231/419430400000), (3033/104857600000), (8907/838860800000), (4071/2097152000000), 0]

def minusWeights0287 : Fin 11 → ℚ := ![(1011/4194304000000), (1011/419430400000), (9099/838860800000), (3033/104857600000), (21231/419430400000), (63693/1048576000000), (21231/419430400000), (3033/104857600000), (9291/838860800000), (6039/2097152000000), (1011/2097152000000)]

theorem checked0287 :
    (∀ i, 0 ≤ plusWeights0287 i) ∧
    (∀ i, 0 ≤ minusWeights0287 i) ∧
    (∀ i, plusCoefficients coefficients0287 upper0287 i = powerCoefficients10 plusWeights0287 i) ∧
    (∀ i, minusCoefficients coefficients0287 upper0287 i = powerCoefficients10 minusWeights0287 i) := by
  decide +kernel

theorem bound0287 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0287 g| ≤ (upper0287 : ℝ) :=
  abs_of_coefficients coefficients0287 upper0287 powerCoefficients10 plusWeights0287 minusWeights0287
    checked0287.1 checked0287.2.1 checked0287.2.2.1 checked0287.2.2.2
    (power_identity10 plusWeights0287) (power_identity10 minusWeights0287) g hg hmax

def envelope0287 : Envelope := ⟨coefficients0287, upper0287, bound0287⟩

end BilayerDressed.CubicQuarticEnvelopes

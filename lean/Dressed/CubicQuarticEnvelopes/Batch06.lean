import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0192 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-315/8192), (-45/4096), (-495/16384), (-225/16384)]

def upper0192 : ℚ := (26127/6553600000000)

def plusWeights0192 : Fin 11 → ℚ := ![(26127/6553600000000), (26127/655360000000), (235143/1310720000000), (78381/163840000000), (548667/655360000000), (1646001/1638400000000), (548667/655360000000), (77751/163840000000), (219879/1310720000000), (5751/204800000000), 0]

def minusWeights0192 : Fin 11 → ℚ := ![(26127/6553600000000), (26127/655360000000), (235143/1310720000000), (78381/163840000000), (548667/655360000000), (1646001/1638400000000), (548667/655360000000), (79011/163840000000), (250407/1310720000000), (84627/1638400000000), (26127/3276800000000)]

theorem checked0192 :
    (∀ i, 0 ≤ plusWeights0192 i) ∧
    (∀ i, 0 ≤ minusWeights0192 i) ∧
    (∀ i, plusCoefficients coefficients0192 upper0192 i = powerCoefficients10 plusWeights0192 i) ∧
    (∀ i, minusCoefficients coefficients0192 upper0192 i = powerCoefficients10 minusWeights0192 i) := by
  decide +kernel

theorem bound0192 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0192 g| ≤ (upper0192 : ℝ) :=
  abs_of_coefficients coefficients0192 upper0192 powerCoefficients10 plusWeights0192 minusWeights0192
    checked0192.1 checked0192.2.1 checked0192.2.2.1 checked0192.2.2.2
    (power_identity10 plusWeights0192) (power_identity10 minusWeights0192) g hg hmax

def envelope0192 : Envelope := ⟨coefficients0192, upper0192, bound0192⟩

def coefficients0193 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-39/1024), (-41/1024), (-619/8192), (-533/16384)]

def upper0193 : ℚ := (702513/163840000000000)

def plusWeights0193 : Fin 11 → ℚ := ![(702513/163840000000000), (702513/16384000000000), (6322617/32768000000000), (2107539/4096000000000), (14752773/16384000000000), (44258319/40960000000000), (14752773/16384000000000), (2091939/4096000000000), (5935097/32768000000000), (100191/3276800000000), 0]

def minusWeights0193 : Fin 11 → ℚ := ![(702513/163840000000000), (702513/16384000000000), (6322617/32768000000000), (2107539/4096000000000), (14752773/16384000000000), (44258319/40960000000000), (14752773/16384000000000), (2123139/4096000000000), (6710137/32768000000000), (904071/16384000000000), (702513/81920000000000)]

theorem checked0193 :
    (∀ i, 0 ≤ plusWeights0193 i) ∧
    (∀ i, 0 ≤ minusWeights0193 i) ∧
    (∀ i, plusCoefficients coefficients0193 upper0193 i = powerCoefficients10 plusWeights0193 i) ∧
    (∀ i, minusCoefficients coefficients0193 upper0193 i = powerCoefficients10 minusWeights0193 i) := by
  decide +kernel

theorem bound0193 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0193 g| ≤ (upper0193 : ℝ) :=
  abs_of_coefficients coefficients0193 upper0193 powerCoefficients10 plusWeights0193 minusWeights0193
    checked0193.1 checked0193.2.1 checked0193.2.2.1 checked0193.2.2.2
    (power_identity10 plusWeights0193) (power_identity10 minusWeights0193) g hg hmax

def envelope0193 : Envelope := ⟨coefficients0193, upper0193, bound0193⟩

def coefficients0194 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-37/1024), (-43/1024), (-261/4096), (-53/2048)]

def upper0194 : ℚ := (41979/10240000000000)

def plusWeights0194 : Fin 11 → ℚ := ![(41979/10240000000000), (41979/1024000000000), (377811/2048000000000), (125937/256000000000), (881559/1024000000000), (2644677/2560000000000), (881559/1024000000000), (31253/64000000000), (354751/2048000000000), (23963/819200000000), 0]

def minusWeights0194 : Fin 11 → ℚ := ![(41979/10240000000000), (41979/1024000000000), (377811/2048000000000), (125937/256000000000), (881559/1024000000000), (2644677/2560000000000), (881559/1024000000000), (63431/128000000000), (400871/2048000000000), (216017/4096000000000), (41979/5120000000000)]

theorem checked0194 :
    (∀ i, 0 ≤ plusWeights0194 i) ∧
    (∀ i, 0 ≤ minusWeights0194 i) ∧
    (∀ i, plusCoefficients coefficients0194 upper0194 i = powerCoefficients10 plusWeights0194 i) ∧
    (∀ i, minusCoefficients coefficients0194 upper0194 i = powerCoefficients10 minusWeights0194 i) := by
  decide +kernel

theorem bound0194 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0194 g| ≤ (upper0194 : ℝ) :=
  abs_of_coefficients coefficients0194 upper0194 powerCoefficients10 plusWeights0194 minusWeights0194
    checked0194.1 checked0194.2.1 checked0194.2.2.1 checked0194.2.2.2
    (power_identity10 plusWeights0194) (power_identity10 minusWeights0194) g hg hmax

def envelope0194 : Envelope := ⟨coefficients0194, upper0194, bound0194⟩

def coefficients0195 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-37/1024), (-43/1024), (-59/1024), (-187/8192)]

def upper0195 : ℚ := (335307/81920000000000)

def plusWeights0195 : Fin 11 → ℚ := ![(335307/81920000000000), (335307/8192000000000), (3017763/16384000000000), (1005921/2048000000000), (7041447/8192000000000), (21124341/20480000000000), (7041447/8192000000000), (998521/2048000000000), (2833283/16384000000000), (47831/1638400000000), 0]

def minusWeights0195 : Fin 11 → ℚ := ![(335307/81920000000000), (335307/8192000000000), (3017763/16384000000000), (1005921/2048000000000), (7041447/8192000000000), (21124341/20480000000000), (7041447/8192000000000), (1013321/2048000000000), (3202243/16384000000000), (431459/8192000000000), (335307/40960000000000)]

theorem checked0195 :
    (∀ i, 0 ≤ plusWeights0195 i) ∧
    (∀ i, 0 ≤ minusWeights0195 i) ∧
    (∀ i, plusCoefficients coefficients0195 upper0195 i = powerCoefficients10 plusWeights0195 i) ∧
    (∀ i, minusCoefficients coefficients0195 upper0195 i = powerCoefficients10 minusWeights0195 i) := by
  decide +kernel

theorem bound0195 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0195 g| ≤ (upper0195 : ℝ) :=
  abs_of_coefficients coefficients0195 upper0195 powerCoefficients10 plusWeights0195 minusWeights0195
    checked0195.1 checked0195.2.1 checked0195.2.2.1 checked0195.2.2.2
    (power_identity10 plusWeights0195) (power_identity10 minusWeights0195) g hg hmax

def envelope0195 : Envelope := ⟨coefficients0195, upper0195, bound0195⟩

def coefficients0196 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-37/1024), (-43/1024), (-397/8192), (-299/16384)]

def upper0196 : ℚ := (669039/163840000000000)

def plusWeights0196 : Fin 11 → ℚ := ![(669039/163840000000000), (669039/16384000000000), (6021351/32768000000000), (2007117/4096000000000), (14049819/16384000000000), (42149457/40960000000000), (14049819/16384000000000), (1992317/4096000000000), (5652391/32768000000000), (95377/3276800000000), 0]

def minusWeights0196 : Fin 11 → ℚ := ![(669039/163840000000000), (669039/16384000000000), (6021351/32768000000000), (2007117/4096000000000), (14049819/16384000000000), (42149457/40960000000000), (14049819/16384000000000), (2021917/4096000000000), (6390311/32768000000000), (861193/16384000000000), (669039/81920000000000)]

theorem checked0196 :
    (∀ i, 0 ≤ plusWeights0196 i) ∧
    (∀ i, 0 ≤ minusWeights0196 i) ∧
    (∀ i, plusCoefficients coefficients0196 upper0196 i = powerCoefficients10 plusWeights0196 i) ∧
    (∀ i, minusCoefficients coefficients0196 upper0196 i = powerCoefficients10 minusWeights0196 i) := by
  decide +kernel

theorem bound0196 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0196 g| ≤ (upper0196 : ℝ) :=
  abs_of_coefficients coefficients0196 upper0196 powerCoefficients10 plusWeights0196 minusWeights0196
    checked0196.1 checked0196.2.1 checked0196.2.2.1 checked0196.2.2.2
    (power_identity10 plusWeights0196) (power_identity10 minusWeights0196) g hg hmax

def envelope0196 : Envelope := ⟨coefficients0196, upper0196, bound0196⟩

def coefficients0197 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/256), (-11/256), (-461/8192), (-357/16384)]

def upper0197 : ℚ := (655977/163840000000000)

def plusWeights0197 : Fin 11 → ℚ := ![(655977/163840000000000), (655977/16384000000000), (5903793/32768000000000), (1967931/4096000000000), (13775517/16384000000000), (41326551/40960000000000), (13775517/16384000000000), (1953531/4096000000000), (5544113/32768000000000), (18727/655360000000), 0]

def minusWeights0197 : Fin 11 → ℚ := ![(655977/163840000000000), (655977/16384000000000), (5903793/32768000000000), (1967931/4096000000000), (13775517/16384000000000), (41326551/40960000000000), (13775517/16384000000000), (1982331/4096000000000), (6263473/32768000000000), (843779/16384000000000), (655977/81920000000000)]

theorem checked0197 :
    (∀ i, 0 ≤ plusWeights0197 i) ∧
    (∀ i, 0 ≤ minusWeights0197 i) ∧
    (∀ i, plusCoefficients coefficients0197 upper0197 i = powerCoefficients10 plusWeights0197 i) ∧
    (∀ i, minusCoefficients coefficients0197 upper0197 i = powerCoefficients10 minusWeights0197 i) := by
  decide +kernel

theorem bound0197 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0197 g| ≤ (upper0197 : ℝ) :=
  abs_of_coefficients coefficients0197 upper0197 powerCoefficients10 plusWeights0197 minusWeights0197
    checked0197.1 checked0197.2.1 checked0197.2.2.1 checked0197.2.2.2
    (power_identity10 plusWeights0197) (power_identity10 minusWeights0197) g hg hmax

def envelope0197 : Envelope := ⟨coefficients0197, upper0197, bound0197⟩

def coefficients0198 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-285/8192), (-15/2048), (-885/32768), (-825/65536)]

def upper0198 : ℚ := (93861/26214400000000)

def plusWeights0198 : Fin 11 → ℚ := ![(93861/26214400000000), (93861/2621440000000), (844749/5242880000000), (281583/655360000000), (1971081/2621440000000), (5913243/6553600000000), (1971081/2621440000000), (279303/655360000000), (157929/1048576000000), (330231/13107200000000), 0]

def minusWeights0198 : Fin 11 → ℚ := ![(93861/26214400000000), (93861/2621440000000), (844749/5242880000000), (281583/655360000000), (1971081/2621440000000), (5913243/6553600000000), (1971081/2621440000000), (283863/655360000000), (899853/5242880000000), (608379/13107200000000), (93861/13107200000000)]

theorem checked0198 :
    (∀ i, 0 ≤ plusWeights0198 i) ∧
    (∀ i, 0 ≤ minusWeights0198 i) ∧
    (∀ i, plusCoefficients coefficients0198 upper0198 i = powerCoefficients10 plusWeights0198 i) ∧
    (∀ i, minusCoefficients coefficients0198 upper0198 i = powerCoefficients10 minusWeights0198 i) := by
  decide +kernel

theorem bound0198 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0198 g| ≤ (upper0198 : ℝ) :=
  abs_of_coefficients coefficients0198 upper0198 powerCoefficients10 plusWeights0198 minusWeights0198
    checked0198.1 checked0198.2.1 checked0198.2.2.1 checked0198.2.2.2
    (power_identity10 plusWeights0198) (power_identity10 minusWeights0198) g hg hmax

def envelope0198 : Envelope := ⟨coefficients0198, upper0198, bound0198⟩

def coefficients0199 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-135/4096), (45/2048), (-255/8192), (-75/4096)]

def upper0199 : ℚ := (2547/819200000000)

def plusWeights0199 : Fin 11 → ℚ := ![(2547/819200000000), (2547/81920000000), (22923/163840000000), (7641/20480000000), (53487/81920000000), (160461/204800000000), (53487/81920000000), (15147/40960000000), (21339/163840000000), (35409/1638400000000), 0]

def minusWeights0199 : Fin 11 → ℚ := ![(2547/819200000000), (2547/81920000000), (22923/163840000000), (7641/20480000000), (53487/81920000000), (160461/204800000000), (53487/81920000000), (15417/40960000000), (24507/163840000000), (66471/1638400000000), (2547/409600000000)]

theorem checked0199 :
    (∀ i, 0 ≤ plusWeights0199 i) ∧
    (∀ i, 0 ≤ minusWeights0199 i) ∧
    (∀ i, plusCoefficients coefficients0199 upper0199 i = powerCoefficients10 plusWeights0199 i) ∧
    (∀ i, minusCoefficients coefficients0199 upper0199 i = powerCoefficients10 minusWeights0199 i) := by
  decide +kernel

theorem bound0199 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0199 g| ≤ (upper0199 : ℝ) :=
  abs_of_coefficients coefficients0199 upper0199 powerCoefficients10 plusWeights0199 minusWeights0199
    checked0199.1 checked0199.2.1 checked0199.2.2.1 checked0199.2.2.2
    (power_identity10 plusWeights0199) (power_identity10 minusWeights0199) g hg hmax

def envelope0199 : Envelope := ⟨coefficients0199, upper0199, bound0199⟩

def coefficients0200 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/512), (-15/512), (-315/2048), (-75/1024)]

def upper0200 : ℚ := (693/204800000000)

def plusWeights0200 : Fin 11 → ℚ := ![(693/204800000000), (693/20480000000), (6237/40960000000), (2079/5120000000), (14553/20480000000), (43659/51200000000), (14553/20480000000), (129/320000000), (1173/8192000000), (9957/409600000000), 0]

def minusWeights0200 : Fin 11 → ℚ := ![(693/204800000000), (693/20480000000), (6237/40960000000), (2079/5120000000), (14553/20480000000), (43659/51200000000), (14553/20480000000), (1047/2560000000), (6609/40960000000), (17763/409600000000), (693/102400000000)]

theorem checked0200 :
    (∀ i, 0 ≤ plusWeights0200 i) ∧
    (∀ i, 0 ≤ minusWeights0200 i) ∧
    (∀ i, plusCoefficients coefficients0200 upper0200 i = powerCoefficients10 plusWeights0200 i) ∧
    (∀ i, minusCoefficients coefficients0200 upper0200 i = powerCoefficients10 minusWeights0200 i) := by
  decide +kernel

theorem bound0200 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0200 g| ≤ (upper0200 : ℝ) :=
  abs_of_coefficients coefficients0200 upper0200 powerCoefficients10 plusWeights0200 minusWeights0200
    checked0200.1 checked0200.2.1 checked0200.2.2.1 checked0200.2.2.2
    (power_identity10 plusWeights0200) (power_identity10 minusWeights0200) g hg hmax

def envelope0200 : Envelope := ⟨coefficients0200, upper0200, bound0200⟩

def coefficients0201 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/512), (-15/512), (-165/2048), (-75/2048)]

def upper0201 : ℚ := (2709/819200000000)

def plusWeights0201 : Fin 11 → ℚ := ![(2709/819200000000), (2709/81920000000), (24381/163840000000), (8127/20480000000), (56889/81920000000), (170667/204800000000), (56889/81920000000), (8067/20480000000), (22893/163840000000), (1209/51200000000), 0]

def minusWeights0201 : Fin 11 → ℚ := ![(2709/819200000000), (2709/81920000000), (24381/163840000000), (8127/20480000000), (56889/81920000000), (170667/204800000000), (56889/81920000000), (8187/20480000000), (25869/163840000000), (8709/204800000000), (2709/409600000000)]

theorem checked0201 :
    (∀ i, 0 ≤ plusWeights0201 i) ∧
    (∀ i, 0 ≤ minusWeights0201 i) ∧
    (∀ i, plusCoefficients coefficients0201 upper0201 i = powerCoefficients10 plusWeights0201 i) ∧
    (∀ i, minusCoefficients coefficients0201 upper0201 i = powerCoefficients10 minusWeights0201 i) := by
  decide +kernel

theorem bound0201 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0201 g| ≤ (upper0201 : ℝ) :=
  abs_of_coefficients coefficients0201 upper0201 powerCoefficients10 plusWeights0201 minusWeights0201
    checked0201.1 checked0201.2.1 checked0201.2.2.1 checked0201.2.2.2
    (power_identity10 plusWeights0201) (power_identity10 minusWeights0201) g hg hmax

def envelope0201 : Envelope := ⟨coefficients0201, upper0201, bound0201⟩

def coefficients0202 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/512), (-15/512), (-1245/16384), (-1125/32768)]

def upper0202 : ℚ := (43281/13107200000000)

def plusWeights0202 : Fin 11 → ℚ := ![(43281/13107200000000), (43281/1310720000000), (389529/2621440000000), (129843/327680000000), (908901/1310720000000), (2726703/3276800000000), (908901/1310720000000), (128883/327680000000), (365721/2621440000000), (154467/6553600000000), 0]

def minusWeights0202 : Fin 11 → ℚ := ![(43281/13107200000000), (43281/1310720000000), (389529/2621440000000), (129843/327680000000), (908901/1310720000000), (2726703/3276800000000), (908901/1310720000000), (130803/327680000000), (413337/2621440000000), (278343/6553600000000), (43281/6553600000000)]

theorem checked0202 :
    (∀ i, 0 ≤ plusWeights0202 i) ∧
    (∀ i, 0 ≤ minusWeights0202 i) ∧
    (∀ i, plusCoefficients coefficients0202 upper0202 i = powerCoefficients10 plusWeights0202 i) ∧
    (∀ i, minusCoefficients coefficients0202 upper0202 i = powerCoefficients10 minusWeights0202 i) := by
  decide +kernel

theorem bound0202 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0202 g| ≤ (upper0202 : ℝ) :=
  abs_of_coefficients coefficients0202 upper0202 powerCoefficients10 plusWeights0202 minusWeights0202
    checked0202.1 checked0202.2.1 checked0202.2.2.1 checked0202.2.2.2
    (power_identity10 plusWeights0202) (power_identity10 minusWeights0202) g hg hmax

def envelope0202 : Envelope := ⟨coefficients0202, upper0202, bound0202⟩

def coefficients0203 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/512), (-15/512), (-585/8192), (-525/16384)]

def upper0203 : ℚ := (21609/6553600000000)

def plusWeights0203 : Fin 11 → ℚ := ![(21609/6553600000000), (21609/655360000000), (194481/1310720000000), (64827/163840000000), (453789/655360000000), (1361367/1638400000000), (453789/655360000000), (64347/163840000000), (182577/1310720000000), (77091/3276800000000), 0]

def minusWeights0203 : Fin 11 → ℚ := ![(21609/6553600000000), (21609/655360000000), (194481/1310720000000), (64827/163840000000), (453789/655360000000), (1361367/1638400000000), (453789/655360000000), (65307/163840000000), (41277/262144000000), (138999/3276800000000), (21609/3276800000000)]

theorem checked0203 :
    (∀ i, 0 ≤ plusWeights0203 i) ∧
    (∀ i, 0 ≤ minusWeights0203 i) ∧
    (∀ i, plusCoefficients coefficients0203 upper0203 i = powerCoefficients10 plusWeights0203 i) ∧
    (∀ i, minusCoefficients coefficients0203 upper0203 i = powerCoefficients10 minusWeights0203 i) := by
  decide +kernel

theorem bound0203 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0203 g| ≤ (upper0203 : ℝ) :=
  abs_of_coefficients coefficients0203 upper0203 powerCoefficients10 plusWeights0203 minusWeights0203
    checked0203.1 checked0203.2.1 checked0203.2.2.1 checked0203.2.2.2
    (power_identity10 plusWeights0203) (power_identity10 minusWeights0203) g hg hmax

def envelope0203 : Envelope := ⟨coefficients0203, upper0203, bound0203⟩

def coefficients0204 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/512), (-15/512), (-255/4096), (-225/8192)]

def upper0204 : ℚ := (10773/3276800000000)

def plusWeights0204 : Fin 11 → ℚ := ![(10773/3276800000000), (10773/327680000000), (96957/655360000000), (32319/81920000000), (226233/327680000000), (678699/819200000000), (226233/327680000000), (32079/81920000000), (18201/131072000000), (38403/1638400000000), 0]

def minusWeights0204 : Fin 11 → ℚ := ![(10773/3276800000000), (10773/327680000000), (96957/655360000000), (32319/81920000000), (226233/327680000000), (678699/819200000000), (226233/327680000000), (32559/81920000000), (102909/655360000000), (69327/1638400000000), (10773/1638400000000)]

theorem checked0204 :
    (∀ i, 0 ≤ plusWeights0204 i) ∧
    (∀ i, 0 ≤ minusWeights0204 i) ∧
    (∀ i, plusCoefficients coefficients0204 upper0204 i = powerCoefficients10 plusWeights0204 i) ∧
    (∀ i, minusCoefficients coefficients0204 upper0204 i = powerCoefficients10 minusWeights0204 i) := by
  decide +kernel

theorem bound0204 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0204 g| ≤ (upper0204 : ℝ) :=
  abs_of_coefficients coefficients0204 upper0204 powerCoefficients10 plusWeights0204 minusWeights0204
    checked0204.1 checked0204.2.1 checked0204.2.2.1 checked0204.2.2.2
    (power_identity10 plusWeights0204) (power_identity10 minusWeights0204) g hg hmax

def envelope0204 : Envelope := ⟨coefficients0204, upper0204, bound0204⟩

def coefficients0205 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/512), (-15/512), (-135/8192), (-75/16384)]

def upper0205 : ℚ := (21231/6553600000000)

def plusWeights0205 : Fin 11 → ℚ := ![(21231/6553600000000), (21231/655360000000), (191079/1310720000000), (63693/163840000000), (445851/655360000000), (1337553/1638400000000), (445851/655360000000), (63213/163840000000), (7167/52428800000), (75381/3276800000000), 0]

def minusWeights0205 : Fin 11 → ℚ := ![(21231/6553600000000), (21231/655360000000), (191079/1310720000000), (63693/163840000000), (445851/655360000000), (1337553/1638400000000), (445851/655360000000), (64173/163840000000), (202983/1310720000000), (136929/3276800000000), (21231/3276800000000)]

theorem checked0205 :
    (∀ i, 0 ≤ plusWeights0205 i) ∧
    (∀ i, 0 ≤ minusWeights0205 i) ∧
    (∀ i, plusCoefficients coefficients0205 upper0205 i = powerCoefficients10 plusWeights0205 i) ∧
    (∀ i, minusCoefficients coefficients0205 upper0205 i = powerCoefficients10 minusWeights0205 i) := by
  decide +kernel

theorem bound0205 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0205 g| ≤ (upper0205 : ℝ) :=
  abs_of_coefficients coefficients0205 upper0205 powerCoefficients10 plusWeights0205 minusWeights0205
    checked0205.1 checked0205.2.1 checked0205.2.2.1 checked0205.2.2.2
    (power_identity10 plusWeights0205) (power_identity10 minusWeights0205) g hg hmax

def envelope0205 : Envelope := ⟨coefficients0205, upper0205, bound0205⟩

def coefficients0206 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/8192), (375/32768), (375/65536), (1875/524288)]

def upper0206 : ℚ := (22029/8388608000000)

def plusWeights0206 : Fin 11 → ℚ := ![(22029/8388608000000), (22029/838860800000), (198261/1677721600000), (66087/209715200000), (462609/838860800000), (1387827/2097152000000), (462609/838860800000), (65511/209715200000), (184629/1677721600000), (76569/4194304000000), 0]

def minusWeights0206 : Fin 11 → ℚ := ![(22029/8388608000000), (22029/838860800000), (198261/1677721600000), (66087/209715200000), (462609/838860800000), (1387827/2097152000000), (462609/838860800000), (66663/209715200000), (211893/1677721600000), (143721/4194304000000), (22029/4194304000000)]

theorem checked0206 :
    (∀ i, 0 ≤ plusWeights0206 i) ∧
    (∀ i, 0 ≤ minusWeights0206 i) ∧
    (∀ i, plusCoefficients coefficients0206 upper0206 i = powerCoefficients10 plusWeights0206 i) ∧
    (∀ i, minusCoefficients coefficients0206 upper0206 i = powerCoefficients10 minusWeights0206 i) := by
  decide +kernel

theorem bound0206 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0206 g| ≤ (upper0206 : ℝ) :=
  abs_of_coefficients coefficients0206 upper0206 powerCoefficients10 plusWeights0206 minusWeights0206
    checked0206.1 checked0206.2.1 checked0206.2.2.1 checked0206.2.2.2
    (power_identity10 plusWeights0206) (power_identity10 minusWeights0206) g hg hmax

def envelope0206 : Envelope := ⟨coefficients0206, upper0206, bound0206⟩

def coefficients0207 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/8192), (375/32768), (375/65536), (4875/524288)]

def upper0207 : ℚ := (110121/41943040000000)

def plusWeights0207 : Fin 11 → ℚ := ![(110121/41943040000000), (110121/4194304000000), (991089/8388608000000), (330363/1048576000000), (2312541/4194304000000), (6937623/10485760000000), (2312541/4194304000000), (327483/1048576000000), (922929/8388608000000), (15309/838860800000), 0]

def minusWeights0207 : Fin 11 → ℚ := ![(110121/41943040000000), (110121/4194304000000), (991089/8388608000000), (330363/1048576000000), (2312541/4194304000000), (6937623/10485760000000), (2312541/4194304000000), (333243/1048576000000), (1059249/8388608000000), (143697/4194304000000), (110121/20971520000000)]

theorem checked0207 :
    (∀ i, 0 ≤ plusWeights0207 i) ∧
    (∀ i, 0 ≤ minusWeights0207 i) ∧
    (∀ i, plusCoefficients coefficients0207 upper0207 i = powerCoefficients10 plusWeights0207 i) ∧
    (∀ i, minusCoefficients coefficients0207 upper0207 i = powerCoefficients10 minusWeights0207 i) := by
  decide +kernel

theorem bound0207 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0207 g| ≤ (upper0207 : ℝ) :=
  abs_of_coefficients coefficients0207 upper0207 powerCoefficients10 plusWeights0207 minusWeights0207
    checked0207.1 checked0207.2.1 checked0207.2.2.1 checked0207.2.2.2
    (power_identity10 plusWeights0207) (power_identity10 minusWeights0207) g hg hmax

def envelope0207 : Envelope := ⟨coefficients0207, upper0207, bound0207⟩

def coefficients0208 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/8192), (1575/32768), (1575/65536), (7875/262144)]

def upper0208 : ℚ := (46953/20971520000000)

def plusWeights0208 : Fin 11 → ℚ := ![(46953/20971520000000), (46953/2097152000000), (422577/4194304000000), (140859/524288000000), (986013/2097152000000), (2958039/5242880000000), (986013/2097152000000), (139419/524288000000), (390033/4194304000000), (158697/10485760000000), 0]

def minusWeights0208 : Fin 11 → ℚ := ![(46953/20971520000000), (46953/2097152000000), (422577/4194304000000), (140859/524288000000), (986013/2097152000000), (2958039/5242880000000), (986013/2097152000000), (142299/524288000000), (455121/4194304000000), (310833/10485760000000), (46953/10485760000000)]

theorem checked0208 :
    (∀ i, 0 ≤ plusWeights0208 i) ∧
    (∀ i, 0 ≤ minusWeights0208 i) ∧
    (∀ i, plusCoefficients coefficients0208 upper0208 i = powerCoefficients10 plusWeights0208 i) ∧
    (∀ i, minusCoefficients coefficients0208 upper0208 i = powerCoefficients10 minusWeights0208 i) := by
  decide +kernel

theorem bound0208 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0208 g| ≤ (upper0208 : ℝ) :=
  abs_of_coefficients coefficients0208 upper0208 powerCoefficients10 plusWeights0208 minusWeights0208
    checked0208.1 checked0208.2.1 checked0208.2.2.1 checked0208.2.2.2
    (power_identity10 plusWeights0208) (power_identity10 minusWeights0208) g hg hmax

def envelope0208 : Envelope := ⟨coefficients0208, upper0208, bound0208⟩

def coefficients0209 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/1024), (-33/1024), (-1227/8192), (-1149/16384)]

def upper0209 : ℚ := (510489/163840000000000)

def plusWeights0209 : Fin 11 → ℚ := ![(510489/163840000000000), (510489/16384000000000), (4594401/32768000000000), (1531467/4096000000000), (10720269/16384000000000), (32160807/40960000000000), (10720269/16384000000000), (1520667/4096000000000), (4324641/32768000000000), (2943/131072000000), 0]

def minusWeights0209 : Fin 11 → ℚ := ![(510489/163840000000000), (510489/16384000000000), (4594401/32768000000000), (1531467/4096000000000), (10720269/16384000000000), (32160807/40960000000000), (10720269/16384000000000), (1542267/4096000000000), (4864161/32768000000000), (653103/16384000000000), (510489/81920000000000)]

theorem checked0209 :
    (∀ i, 0 ≤ plusWeights0209 i) ∧
    (∀ i, 0 ≤ minusWeights0209 i) ∧
    (∀ i, plusCoefficients coefficients0209 upper0209 i = powerCoefficients10 plusWeights0209 i) ∧
    (∀ i, minusCoefficients coefficients0209 upper0209 i = powerCoefficients10 minusWeights0209 i) := by
  decide +kernel

theorem bound0209 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0209 g| ≤ (upper0209 : ℝ) :=
  abs_of_coefficients coefficients0209 upper0209 powerCoefficients10 plusWeights0209 minusWeights0209
    checked0209.1 checked0209.2.1 checked0209.2.2.1 checked0209.2.2.2
    (power_identity10 plusWeights0209) (power_identity10 minusWeights0209) g hg hmax

def envelope0209 : Envelope := ⟨coefficients0209, upper0209, bound0209⟩

def coefficients0210 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/1024), (-33/1024), (-9/64), (-537/8192)]

def upper0210 : ℚ := (254457/81920000000000)

def plusWeights0210 : Fin 11 → ℚ := ![(254457/81920000000000), (254457/8192000000000), (2290113/16384000000000), (763371/2048000000000), (5343597/8192000000000), (16030791/20480000000000), (5343597/8192000000000), (757971/2048000000000), (2155233/16384000000000), (7329/327680000000), 0]

def minusWeights0210 : Fin 11 → ℚ := ![(254457/81920000000000), (254457/8192000000000), (2290113/16384000000000), (763371/2048000000000), (5343597/8192000000000), (16030791/20480000000000), (5343597/8192000000000), (768771/2048000000000), (2424993/16384000000000), (325689/8192000000000), (254457/40960000000000)]

theorem checked0210 :
    (∀ i, 0 ≤ plusWeights0210 i) ∧
    (∀ i, 0 ≤ minusWeights0210 i) ∧
    (∀ i, plusCoefficients coefficients0210 upper0210 i = powerCoefficients10 plusWeights0210 i) ∧
    (∀ i, minusCoefficients coefficients0210 upper0210 i = powerCoefficients10 minusWeights0210 i) := by
  decide +kernel

theorem bound0210 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0210 g| ≤ (upper0210 : ℝ) :=
  abs_of_coefficients coefficients0210 upper0210 powerCoefficients10 plusWeights0210 minusWeights0210
    checked0210.1 checked0210.2.1 checked0210.2.2.1 checked0210.2.2.2
    (power_identity10 plusWeights0210) (power_identity10 minusWeights0210) g hg hmax

def envelope0210 : Envelope := ⟨coefficients0210, upper0210, bound0210⟩

def coefficients0211 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/1024), (-33/1024), (-1929/16384), (-1773/32768)]

def upper0211 : ℚ := (1009953/327680000000000)

def plusWeights0211 : Fin 11 → ℚ := ![(1009953/327680000000000), (1009953/32768000000000), (9089577/65536000000000), (3029859/8192000000000), (21209013/32768000000000), (63627039/81920000000000), (21209013/32768000000000), (3008259/8192000000000), (8550057/65536000000000), (29031/1310720000000), 0]

def minusWeights0211 : Fin 11 → ℚ := ![(1009953/327680000000000), (1009953/32768000000000), (9089577/65536000000000), (3029859/8192000000000), (21209013/32768000000000), (63627039/81920000000000), (21209013/32768000000000), (3051459/8192000000000), (9629097/65536000000000), (1294131/32768000000000), (1009953/163840000000000)]

theorem checked0211 :
    (∀ i, 0 ≤ plusWeights0211 i) ∧
    (∀ i, 0 ≤ minusWeights0211 i) ∧
    (∀ i, plusCoefficients coefficients0211 upper0211 i = powerCoefficients10 plusWeights0211 i) ∧
    (∀ i, minusCoefficients coefficients0211 upper0211 i = powerCoefficients10 minusWeights0211 i) := by
  decide +kernel

theorem bound0211 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0211 g| ≤ (upper0211 : ℝ) :=
  abs_of_coefficients coefficients0211 upper0211 powerCoefficients10 plusWeights0211 minusWeights0211
    checked0211.1 checked0211.2.1 checked0211.2.2.1 checked0211.2.2.2
    (power_identity10 plusWeights0211) (power_identity10 minusWeights0211) g hg hmax

def envelope0211 : Envelope := ⟨coefficients0211, upper0211, bound0211⟩

def coefficients0212 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-105/4096), (-15/2048), (-255/16384), (-225/32768)]

def upper0212 : ℚ := (34773/13107200000000)

def plusWeights0212 : Fin 11 → ℚ := ![(34773/13107200000000), (34773/1310720000000), (312957/2621440000000), (104319/327680000000), (730233/1310720000000), (2190699/3276800000000), (730233/1310720000000), (103479/327680000000), (58521/524288000000), (122403/6553600000000), 0]

def minusWeights0212 : Fin 11 → ℚ := ![(34773/13107200000000), (34773/1310720000000), (312957/2621440000000), (104319/327680000000), (730233/1310720000000), (2190699/3276800000000), (730233/1310720000000), (105159/327680000000), (333309/2621440000000), (225327/6553600000000), (34773/6553600000000)]

theorem checked0212 :
    (∀ i, 0 ≤ plusWeights0212 i) ∧
    (∀ i, 0 ≤ minusWeights0212 i) ∧
    (∀ i, plusCoefficients coefficients0212 upper0212 i = powerCoefficients10 plusWeights0212 i) ∧
    (∀ i, minusCoefficients coefficients0212 upper0212 i = powerCoefficients10 minusWeights0212 i) := by
  decide +kernel

theorem bound0212 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0212 g| ≤ (upper0212 : ℝ) :=
  abs_of_coefficients coefficients0212 upper0212 powerCoefficients10 plusWeights0212 minusWeights0212
    checked0212.1 checked0212.2.1 checked0212.2.2.1 checked0212.2.2.2
    (power_identity10 plusWeights0212) (power_identity10 minusWeights0212) g hg hmax

def envelope0212 : Envelope := ⟨coefficients0212, upper0212, bound0212⟩

def coefficients0213 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-203/8192), (-19/1024), (-1049/32768), (-873/65536)]

def upper0213 : ℚ := (1767453/655360000000000)

def plusWeights0213 : Fin 11 → ℚ := ![(1767453/655360000000000), (1767453/65536000000000), (15907077/131072000000000), (5302359/16384000000000), (37116513/65536000000000), (111349539/163840000000000), (37116513/65536000000000), (5261759/16384000000000), (14908357/131072000000000), (250767/13107200000000), 0]

def minusWeights0213 : Fin 11 → ℚ := ![(1767453/655360000000000), (1767453/65536000000000), (15907077/131072000000000), (5302359/16384000000000), (37116513/65536000000000), (111349539/163840000000000), (37116513/65536000000000), (5342959/16384000000000), (16905797/131072000000000), (2281071/65536000000000), (1767453/327680000000000)]

theorem checked0213 :
    (∀ i, 0 ≤ plusWeights0213 i) ∧
    (∀ i, 0 ≤ minusWeights0213 i) ∧
    (∀ i, plusCoefficients coefficients0213 upper0213 i = powerCoefficients10 plusWeights0213 i) ∧
    (∀ i, minusCoefficients coefficients0213 upper0213 i = powerCoefficients10 minusWeights0213 i) := by
  decide +kernel

theorem bound0213 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0213 g| ≤ (upper0213 : ℝ) :=
  abs_of_coefficients coefficients0213 upper0213 powerCoefficients10 plusWeights0213 minusWeights0213
    checked0213.1 checked0213.2.1 checked0213.2.2.1 checked0213.2.2.2
    (power_identity10 plusWeights0213) (power_identity10 minusWeights0213) g hg hmax

def envelope0213 : Envelope := ⟨coefficients0213, upper0213, bound0213⟩

def coefficients0214 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-3/128), (-13/512), (-803/16384), (-691/32768)]

def upper0214 : ℚ := (867951/327680000000000)

def plusWeights0214 : Fin 11 → ℚ := ![(867951/327680000000000), (867951/32768000000000), (7811559/65536000000000), (2603853/8192000000000), (18226971/32768000000000), (54680913/81920000000000), (18226971/32768000000000), (2584653/8192000000000), (7334119/65536000000000), (123861/6553600000000), 0]

def minusWeights0214 : Fin 11 → ℚ := ![(867951/327680000000000), (867951/32768000000000), (7811559/65536000000000), (2603853/8192000000000), (18226971/32768000000000), (54680913/81920000000000), (18226971/32768000000000), (2623053/8192000000000), (8288999/65536000000000), (1116597/32768000000000), (867951/163840000000000)]

theorem checked0214 :
    (∀ i, 0 ≤ plusWeights0214 i) ∧
    (∀ i, 0 ≤ minusWeights0214 i) ∧
    (∀ i, plusCoefficients coefficients0214 upper0214 i = powerCoefficients10 plusWeights0214 i) ∧
    (∀ i, minusCoefficients coefficients0214 upper0214 i = powerCoefficients10 minusWeights0214 i) := by
  decide +kernel

theorem bound0214 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0214 g| ≤ (upper0214 : ℝ) :=
  abs_of_coefficients coefficients0214 upper0214 powerCoefficients10 plusWeights0214 minusWeights0214
    checked0214.1 checked0214.2.1 checked0214.2.2.1 checked0214.2.2.2
    (power_identity10 plusWeights0214) (power_identity10 minusWeights0214) g hg hmax

def envelope0214 : Envelope := ⟨coefficients0214, upper0214, bound0214⟩

def coefficients0215 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-95/4096), (-5/1024), (-1195/16384), (-1175/32768)]

def upper0215 : ℚ := (32043/13107200000000)

def plusWeights0215 : Fin 11 → ℚ := ![(32043/13107200000000), (32043/1310720000000), (288387/2621440000000), (96129/327680000000), (672903/1310720000000), (2018709/3276800000000), (672903/1310720000000), (95369/327680000000), (270019/2621440000000), (113497/6553600000000), 0]

def minusWeights0215 : Fin 11 → ℚ := ![(32043/13107200000000), (32043/1310720000000), (288387/2621440000000), (96129/327680000000), (672903/1310720000000), (2018709/3276800000000), (672903/1310720000000), (96889/327680000000), (61351/524288000000), (206933/6553600000000), (32043/6553600000000)]

theorem checked0215 :
    (∀ i, 0 ≤ plusWeights0215 i) ∧
    (∀ i, 0 ≤ minusWeights0215 i) ∧
    (∀ i, plusCoefficients coefficients0215 upper0215 i = powerCoefficients10 plusWeights0215 i) ∧
    (∀ i, minusCoefficients coefficients0215 upper0215 i = powerCoefficients10 minusWeights0215 i) := by
  decide +kernel

theorem bound0215 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0215 g| ≤ (upper0215 : ℝ) :=
  abs_of_coefficients coefficients0215 upper0215 powerCoefficients10 plusWeights0215 minusWeights0215
    checked0215.1 checked0215.2.1 checked0215.2.2.1 checked0215.2.2.2
    (power_identity10 plusWeights0215) (power_identity10 minusWeights0215) g hg hmax

def envelope0215 : Envelope := ⟨coefficients0215, upper0215, bound0215⟩

def coefficients0216 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-95/4096), (-5/1024), (-295/16384), (-275/32768)]

def upper0216 : ℚ := (31287/13107200000000)

def plusWeights0216 : Fin 11 → ℚ := ![(31287/13107200000000), (31287/1310720000000), (281583/2621440000000), (93861/327680000000), (657027/1310720000000), (1971081/3276800000000), (657027/1310720000000), (93101/327680000000), (52643/524288000000), (110077/6553600000000), 0]

def minusWeights0216 : Fin 11 → ℚ := ![(31287/13107200000000), (31287/1310720000000), (281583/2621440000000), (93861/327680000000), (657027/1310720000000), (1971081/3276800000000), (657027/1310720000000), (94621/327680000000), (299951/2621440000000), (202793/6553600000000), (31287/6553600000000)]

theorem checked0216 :
    (∀ i, 0 ≤ plusWeights0216 i) ∧
    (∀ i, 0 ≤ minusWeights0216 i) ∧
    (∀ i, plusCoefficients coefficients0216 upper0216 i = powerCoefficients10 plusWeights0216 i) ∧
    (∀ i, minusCoefficients coefficients0216 upper0216 i = powerCoefficients10 minusWeights0216 i) := by
  decide +kernel

theorem bound0216 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0216 g| ≤ (upper0216 : ℝ) :=
  abs_of_coefficients coefficients0216 upper0216 powerCoefficients10 plusWeights0216 minusWeights0216
    checked0216.1 checked0216.2.1 checked0216.2.2.1 checked0216.2.2.2
    (power_identity10 plusWeights0216) (power_identity10 minusWeights0216) g hg hmax

def envelope0216 : Envelope := ⟨coefficients0216, upper0216, bound0216⟩

def coefficients0217 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-47/2048), (-53/2048), (-667/16384), (-549/32768)]

def upper0217 : ℚ := (850689/327680000000000)

def plusWeights0217 : Fin 11 → ℚ := ![(850689/327680000000000), (850689/32768000000000), (7656201/65536000000000), (2552067/8192000000000), (17864469/32768000000000), (53593407/81920000000000), (17864469/32768000000000), (2533267/8192000000000), (7188041/65536000000000), (121359/6553600000000), 0]

def minusWeights0217 : Fin 11 → ℚ := ![(850689/327680000000000), (850689/32768000000000), (7656201/65536000000000), (2552067/8192000000000), (17864469/32768000000000), (53593407/81920000000000), (17864469/32768000000000), (2570867/8192000000000), (8124361/65536000000000), (1094583/32768000000000), (850689/163840000000000)]

theorem checked0217 :
    (∀ i, 0 ≤ plusWeights0217 i) ∧
    (∀ i, 0 ≤ minusWeights0217 i) ∧
    (∀ i, plusCoefficients coefficients0217 upper0217 i = powerCoefficients10 plusWeights0217 i) ∧
    (∀ i, minusCoefficients coefficients0217 upper0217 i = powerCoefficients10 minusWeights0217 i) := by
  decide +kernel

theorem bound0217 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0217 g| ≤ (upper0217 : ℝ) :=
  abs_of_coefficients coefficients0217 upper0217 powerCoefficients10 plusWeights0217 minusWeights0217
    checked0217.1 checked0217.2.1 checked0217.2.2.1 checked0217.2.2.2
    (power_identity10 plusWeights0217) (power_identity10 minusWeights0217) g hg hmax

def envelope0217 : Envelope := ⟨coefficients0217, upper0217, bound0217⟩

def coefficients0218 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-47/2048), (-53/2048), (-123/4096), (-187/16384)]

def upper0218 : ℚ := (423507/163840000000000)

def plusWeights0218 : Fin 11 → ℚ := ![(423507/163840000000000), (423507/16384000000000), (3811563/32768000000000), (1270521/4096000000000), (8893647/16384000000000), (26680941/40960000000000), (8893647/16384000000000), (1261121/4096000000000), (3577483/32768000000000), (60347/3276800000000), 0]

def minusWeights0218 : Fin 11 → ℚ := ![(423507/163840000000000), (423507/16384000000000), (3811563/32768000000000), (1270521/4096000000000), (8893647/16384000000000), (26680941/40960000000000), (8893647/16384000000000), (1279921/4096000000000), (4045643/32768000000000), (545279/16384000000000), (423507/81920000000000)]

theorem checked0218 :
    (∀ i, 0 ≤ plusWeights0218 i) ∧
    (∀ i, 0 ≤ minusWeights0218 i) ∧
    (∀ i, plusCoefficients coefficients0218 upper0218 i = powerCoefficients10 plusWeights0218 i) ∧
    (∀ i, minusCoefficients coefficients0218 upper0218 i = powerCoefficients10 minusWeights0218 i) := by
  decide +kernel

theorem bound0218 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0218 g| ≤ (upper0218 : ℝ) :=
  abs_of_coefficients coefficients0218 upper0218 powerCoefficients10 plusWeights0218 minusWeights0218
    checked0218.1 checked0218.2.1 checked0218.2.2.1 checked0218.2.2.2
    (power_identity10 plusWeights0218) (power_identity10 minusWeights0218) g hg hmax

def envelope0218 : Envelope := ⟨coefficients0218, upper0218, bound0218⟩

def coefficients0219 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-47/2048), (-53/2048), (-417/16384), (-299/32768)]

def upper0219 : ℚ := (845439/327680000000000)

def plusWeights0219 : Fin 11 → ℚ := ![(845439/327680000000000), (845439/32768000000000), (7608951/65536000000000), (2536317/8192000000000), (17754219/32768000000000), (53262657/81920000000000), (17754219/32768000000000), (2517517/8192000000000), (7140791/65536000000000), (120409/6553600000000), 0]

def minusWeights0219 : Fin 11 → ℚ := ![(845439/327680000000000), (845439/32768000000000), (7608951/65536000000000), (2536317/8192000000000), (17754219/32768000000000), (53262657/81920000000000), (17754219/32768000000000), (2555117/8192000000000), (8077111/65536000000000), (1088833/32768000000000), (845439/163840000000000)]

theorem checked0219 :
    (∀ i, 0 ≤ plusWeights0219 i) ∧
    (∀ i, 0 ≤ minusWeights0219 i) ∧
    (∀ i, plusCoefficients coefficients0219 upper0219 i = powerCoefficients10 plusWeights0219 i) ∧
    (∀ i, minusCoefficients coefficients0219 upper0219 i = powerCoefficients10 minusWeights0219 i) := by
  decide +kernel

theorem bound0219 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0219 g| ≤ (upper0219 : ℝ) :=
  abs_of_coefficients coefficients0219 upper0219 powerCoefficients10 plusWeights0219 minusWeights0219
    checked0219.1 checked0219.2.1 checked0219.2.2.1 checked0219.2.2.2
    (power_identity10 plusWeights0219) (power_identity10 minusWeights0219) g hg hmax

def envelope0219 : Envelope := ⟨coefficients0219, upper0219, bound0219⟩

def coefficients0220 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-45/2048), (-55/2048), (-155/4096), (-245/16384)]

def upper0220 : ℚ := (82089/32768000000000)

def plusWeights0220 : Fin 11 → ℚ := ![(82089/32768000000000), (82089/3276800000000), (738801/6553600000000), (246267/819200000000), (1723869/3276800000000), (5171607/8192000000000), (1723869/3276800000000), (244467/819200000000), (693841/6553600000000), (11721/655360000000), 0]

def minusWeights0220 : Fin 11 → ℚ := ![(82089/32768000000000), (82089/3276800000000), (738801/6553600000000), (246267/819200000000), (1723869/3276800000000), (5171607/8192000000000), (1723869/3276800000000), (248067/819200000000), (783761/6553600000000), (105573/3276800000000), (82089/16384000000000)]

theorem checked0220 :
    (∀ i, 0 ≤ plusWeights0220 i) ∧
    (∀ i, 0 ≤ minusWeights0220 i) ∧
    (∀ i, plusCoefficients coefficients0220 upper0220 i = powerCoefficients10 plusWeights0220 i) ∧
    (∀ i, minusCoefficients coefficients0220 upper0220 i = powerCoefficients10 minusWeights0220 i) := by
  decide +kernel

theorem bound0220 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0220 g| ≤ (upper0220 : ℝ) :=
  abs_of_coefficients coefficients0220 upper0220 powerCoefficients10 plusWeights0220 minusWeights0220
    checked0220.1 checked0220.2.1 checked0220.2.2.1 checked0220.2.2.2
    (power_identity10 plusWeights0220) (power_identity10 minusWeights0220) g hg hmax

def envelope0220 : Envelope := ⟨coefficients0220, upper0220, bound0220⟩

def coefficients0221 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-45/2048), (-45/2048), (-1005/32768), (-825/65536)]

def upper0221 : ℚ := (64197/26214400000000)

def plusWeights0221 : Fin 11 → ℚ := ![(64197/26214400000000), (64197/2621440000000), (577773/5242880000000), (192591/655360000000), (1348137/2621440000000), (4044411/6553600000000), (1348137/2621440000000), (191151/655360000000), (542061/5242880000000), (228423/13107200000000), 0]

def minusWeights0221 : Fin 11 → ℚ := ![(64197/26214400000000), (64197/2621440000000), (577773/5242880000000), (192591/655360000000), (1348137/2621440000000), (4044411/6553600000000), (1348137/2621440000000), (194031/655360000000), (122697/1048576000000), (413547/13107200000000), (64197/13107200000000)]

theorem checked0221 :
    (∀ i, 0 ≤ plusWeights0221 i) ∧
    (∀ i, 0 ≤ minusWeights0221 i) ∧
    (∀ i, plusCoefficients coefficients0221 upper0221 i = powerCoefficients10 plusWeights0221 i) ∧
    (∀ i, minusCoefficients coefficients0221 upper0221 i = powerCoefficients10 minusWeights0221 i) := by
  decide +kernel

theorem bound0221 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0221 g| ≤ (upper0221 : ℝ) :=
  abs_of_coefficients coefficients0221 upper0221 powerCoefficients10 plusWeights0221 minusWeights0221
    checked0221.1 checked0221.2.1 checked0221.2.2.1 checked0221.2.2.2
    (power_identity10 plusWeights0221) (power_identity10 minusWeights0221) g hg hmax

def envelope0221 : Envelope := ⟨coefficients0221, upper0221, bound0221⟩

def coefficients0222 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-45/2048), (-45/2048), (-315/16384), (-225/32768)]

def upper0222 : ℚ := (31941/13107200000000)

def plusWeights0222 : Fin 11 → ℚ := ![(31941/13107200000000), (31941/1310720000000), (287469/2621440000000), (95823/327680000000), (670761/1310720000000), (2012283/3276800000000), (670761/1310720000000), (95103/327680000000), (269613/2621440000000), (113499/6553600000000), 0]

def minusWeights0222 : Fin 11 → ℚ := ![(31941/13107200000000), (31941/1310720000000), (287469/2621440000000), (95823/327680000000), (670761/1310720000000), (2012283/3276800000000), (670761/1310720000000), (96543/327680000000), (12213/104857600000), (205911/6553600000000), (31941/6553600000000)]

theorem checked0222 :
    (∀ i, 0 ≤ plusWeights0222 i) ∧
    (∀ i, 0 ≤ minusWeights0222 i) ∧
    (∀ i, plusCoefficients coefficients0222 upper0222 i = powerCoefficients10 plusWeights0222 i) ∧
    (∀ i, minusCoefficients coefficients0222 upper0222 i = powerCoefficients10 minusWeights0222 i) := by
  decide +kernel

theorem bound0222 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0222 g| ≤ (upper0222 : ℝ) :=
  abs_of_coefficients coefficients0222 upper0222 powerCoefficients10 plusWeights0222 minusWeights0222
    checked0222.1 checked0222.2.1 checked0222.2.2.1 checked0222.2.2.2
    (power_identity10 plusWeights0222) (power_identity10 minusWeights0222) g hg hmax

def envelope0222 : Envelope := ⟨coefficients0222, upper0222, bound0222⟩

def coefficients0223 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/256), (-5/256), (-35/2048), (-25/4096)]

def upper0223 : ℚ := (3549/1638400000000)

def plusWeights0223 : Fin 11 → ℚ := ![(3549/1638400000000), (3549/163840000000), (31941/327680000000), (10647/40960000000), (74529/163840000000), (223587/409600000000), (74529/163840000000), (10567/40960000000), (29957/327680000000), (12611/819200000000), 0]

def minusWeights0223 : Fin 11 → ℚ := ![(3549/1638400000000), (3549/163840000000), (31941/327680000000), (10647/40960000000), (74529/163840000000), (223587/409600000000), (74529/163840000000), (10727/40960000000), (1357/13107200000), (22879/819200000000), (3549/819200000000)]

theorem checked0223 :
    (∀ i, 0 ≤ plusWeights0223 i) ∧
    (∀ i, 0 ≤ minusWeights0223 i) ∧
    (∀ i, plusCoefficients coefficients0223 upper0223 i = powerCoefficients10 plusWeights0223 i) ∧
    (∀ i, minusCoefficients coefficients0223 upper0223 i = powerCoefficients10 minusWeights0223 i) := by
  decide +kernel

theorem bound0223 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0223 g| ≤ (upper0223 : ℝ) :=
  abs_of_coefficients coefficients0223 upper0223 powerCoefficients10 plusWeights0223 minusWeights0223
    checked0223.1 checked0223.2.1 checked0223.2.2.1 checked0223.2.2.2
    (power_identity10 plusWeights0223) (power_identity10 minusWeights0223) g hg hmax

def envelope0223 : Envelope := ⟨coefficients0223, upper0223, bound0223⟩

end BilayerDressed.CubicQuarticEnvelopes

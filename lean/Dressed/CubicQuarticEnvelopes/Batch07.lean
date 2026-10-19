import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0224 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-39/2048), (-41/2048), (-269/16384), (-183/32768)]

def upper0224 : ℚ := (695163/327680000000000)

def plusWeights0224 : Fin 11 → ℚ := ![(695163/327680000000000), (695163/32768000000000), (6256467/65536000000000), (2085489/8192000000000), (14598423/32768000000000), (43795269/81920000000000), (14598423/32768000000000), (2069889/8192000000000), (5868947/65536000000000), (98861/6553600000000), 0]

def minusWeights0224 : Fin 11 → ℚ := ![(695163/327680000000000), (695163/32768000000000), (6256467/65536000000000), (2085489/8192000000000), (14598423/32768000000000), (43795269/81920000000000), (14598423/32768000000000), (2101089/8192000000000), (6643987/65536000000000), (896021/32768000000000), (695163/163840000000000)]

theorem checked0224 :
    (∀ i, 0 ≤ plusWeights0224 i) ∧
    (∀ i, 0 ≤ minusWeights0224 i) ∧
    (∀ i, plusCoefficients coefficients0224 upper0224 i = powerCoefficients10 plusWeights0224 i) ∧
    (∀ i, minusCoefficients coefficients0224 upper0224 i = powerCoefficients10 minusWeights0224 i) := by
  decide +kernel

theorem bound0224 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0224 g| ≤ (upper0224 : ℝ) :=
  abs_of_coefficients coefficients0224 upper0224 powerCoefficients10 plusWeights0224 minusWeights0224
    checked0224.1 checked0224.2.1 checked0224.2.2.1 checked0224.2.2.2
    (power_identity10 plusWeights0224) (power_identity10 minusWeights0224) g hg hmax

def envelope0224 : Envelope := ⟨coefficients0224, upper0224, bound0224⟩

def coefficients0225 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/4096), 0, (-375/32768), (-375/65536)]

def upper0225 : ℚ := (9663/5242880000000)

def plusWeights0225 : Fin 11 → ℚ := ![(9663/5242880000000), (9663/524288000000), (86967/1048576000000), (28989/131072000000), (202923/524288000000), (608769/1310720000000), (202923/524288000000), (28749/131072000000), (81207/1048576000000), (6777/524288000000), 0]

def minusWeights0225 : Fin 11 → ℚ := ![(9663/5242880000000), (9663/524288000000), (86967/1048576000000), (28989/131072000000), (202923/524288000000), (608769/1310720000000), (202923/524288000000), (29229/131072000000), (92727/1048576000000), (12549/524288000000), (9663/2621440000000)]

theorem checked0225 :
    (∀ i, 0 ≤ plusWeights0225 i) ∧
    (∀ i, 0 ≤ minusWeights0225 i) ∧
    (∀ i, plusCoefficients coefficients0225 upper0225 i = powerCoefficients10 plusWeights0225 i) ∧
    (∀ i, minusCoefficients coefficients0225 upper0225 i = powerCoefficients10 minusWeights0225 i) := by
  decide +kernel

theorem bound0225 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0225 g| ≤ (upper0225 : ℝ) :=
  abs_of_coefficients coefficients0225 upper0225 powerCoefficients10 plusWeights0225 minusWeights0225
    checked0225.1 checked0225.2.1 checked0225.2.2.1 checked0225.2.2.2
    (power_identity10 plusWeights0225) (power_identity10 minusWeights0225) g hg hmax

def envelope0225 : Envelope := ⟨coefficients0225, upper0225, bound0225⟩

def coefficients0226 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/4096), (225/16384), (225/32768), (1125/262144)]

def upper0226 : ℚ := (35367/20971520000000)

def plusWeights0226 : Fin 11 → ℚ := ![(35367/20971520000000), (35367/2097152000000), (318303/4194304000000), (106101/524288000000), (742707/2097152000000), (2228121/5242880000000), (742707/2097152000000), (105141/524288000000), (295839/4194304000000), (122187/10485760000000), 0]

def minusWeights0226 : Fin 11 → ℚ := ![(35367/20971520000000), (35367/2097152000000), (318303/4194304000000), (106101/524288000000), (742707/2097152000000), (2228121/5242880000000), (742707/2097152000000), (107061/524288000000), (340767/4194304000000), (231483/10485760000000), (35367/10485760000000)]

theorem checked0226 :
    (∀ i, 0 ≤ plusWeights0226 i) ∧
    (∀ i, 0 ≤ minusWeights0226 i) ∧
    (∀ i, plusCoefficients coefficients0226 upper0226 i = powerCoefficients10 plusWeights0226 i) ∧
    (∀ i, minusCoefficients coefficients0226 upper0226 i = powerCoefficients10 minusWeights0226 i) := by
  decide +kernel

theorem bound0226 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0226 g| ≤ (upper0226 : ℝ) :=
  abs_of_coefficients coefficients0226 upper0226 powerCoefficients10 plusWeights0226 minusWeights0226
    checked0226.1 checked0226.2.1 checked0226.2.2.1 checked0226.2.2.2
    (power_identity10 plusWeights0226) (power_identity10 minusWeights0226) g hg hmax

def envelope0226 : Envelope := ⟨coefficients0226, upper0226, bound0226⟩

def coefficients0227 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-37/2048), (-43/2048), (-59/2048), (-187/16384)]

def upper0227 : ℚ := (335307/163840000000000)

def plusWeights0227 : Fin 11 → ℚ := ![(335307/163840000000000), (335307/16384000000000), (3017763/32768000000000), (1005921/4096000000000), (7041447/16384000000000), (21124341/40960000000000), (7041447/16384000000000), (998521/4096000000000), (2833283/32768000000000), (47831/3276800000000), 0]

def minusWeights0227 : Fin 11 → ℚ := ![(335307/163840000000000), (335307/16384000000000), (3017763/32768000000000), (1005921/4096000000000), (7041447/16384000000000), (21124341/40960000000000), (7041447/16384000000000), (1013321/4096000000000), (3202243/32768000000000), (431459/16384000000000), (335307/81920000000000)]

theorem checked0227 :
    (∀ i, 0 ≤ plusWeights0227 i) ∧
    (∀ i, 0 ≤ minusWeights0227 i) ∧
    (∀ i, plusCoefficients coefficients0227 upper0227 i = powerCoefficients10 plusWeights0227 i) ∧
    (∀ i, minusCoefficients coefficients0227 upper0227 i = powerCoefficients10 minusWeights0227 i) := by
  decide +kernel

theorem bound0227 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0227 g| ≤ (upper0227 : ℝ) :=
  abs_of_coefficients coefficients0227 upper0227 powerCoefficients10 plusWeights0227 minusWeights0227
    checked0227.1 checked0227.2.1 checked0227.2.2.1 checked0227.2.2.2
    (power_identity10 plusWeights0227) (power_identity10 minusWeights0227) g hg hmax

def envelope0227 : Envelope := ⟨coefficients0227, upper0227, bound0227⟩

def coefficients0228 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-37/2048), (-43/2048), (-397/16384), (-299/32768)]

def upper0228 : ℚ := (669039/327680000000000)

def plusWeights0228 : Fin 11 → ℚ := ![(669039/327680000000000), (669039/32768000000000), (6021351/65536000000000), (2007117/8192000000000), (14049819/32768000000000), (42149457/81920000000000), (14049819/32768000000000), (1992317/8192000000000), (5652391/65536000000000), (95377/6553600000000), 0]

def minusWeights0228 : Fin 11 → ℚ := ![(669039/327680000000000), (669039/32768000000000), (6021351/65536000000000), (2007117/8192000000000), (14049819/32768000000000), (42149457/81920000000000), (14049819/32768000000000), (2021917/8192000000000), (6390311/65536000000000), (861193/32768000000000), (669039/163840000000000)]

theorem checked0228 :
    (∀ i, 0 ≤ plusWeights0228 i) ∧
    (∀ i, 0 ≤ minusWeights0228 i) ∧
    (∀ i, plusCoefficients coefficients0228 upper0228 i = powerCoefficients10 plusWeights0228 i) ∧
    (∀ i, minusCoefficients coefficients0228 upper0228 i = powerCoefficients10 minusWeights0228 i) := by
  decide +kernel

theorem bound0228 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0228 g| ≤ (upper0228 : ℝ) :=
  abs_of_coefficients coefficients0228 upper0228 powerCoefficients10 plusWeights0228 minusWeights0228
    checked0228.1 checked0228.2.1 checked0228.2.2.1 checked0228.2.2.2
    (power_identity10 plusWeights0228) (power_identity10 minusWeights0228) g hg hmax

def envelope0228 : Envelope := ⟨coefficients0228, upper0228, bound0228⟩

def coefficients0229 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/1024), (-15/1024), (-165/4096), (-75/4096)]

def upper0229 : ℚ := (2709/1638400000000)

def plusWeights0229 : Fin 11 → ℚ := ![(2709/1638400000000), (2709/163840000000), (24381/327680000000), (8127/40960000000), (56889/163840000000), (170667/409600000000), (56889/163840000000), (8067/40960000000), (22893/327680000000), (1209/102400000000), 0]

def minusWeights0229 : Fin 11 → ℚ := ![(2709/1638400000000), (2709/163840000000), (24381/327680000000), (8127/40960000000), (56889/163840000000), (170667/409600000000), (56889/163840000000), (8187/40960000000), (25869/327680000000), (8709/409600000000), (2709/819200000000)]

theorem checked0229 :
    (∀ i, 0 ≤ plusWeights0229 i) ∧
    (∀ i, 0 ≤ minusWeights0229 i) ∧
    (∀ i, plusCoefficients coefficients0229 upper0229 i = powerCoefficients10 plusWeights0229 i) ∧
    (∀ i, minusCoefficients coefficients0229 upper0229 i = powerCoefficients10 minusWeights0229 i) := by
  decide +kernel

theorem bound0229 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0229 g| ≤ (upper0229 : ℝ) :=
  abs_of_coefficients coefficients0229 upper0229 powerCoefficients10 plusWeights0229 minusWeights0229
    checked0229.1 checked0229.2.1 checked0229.2.2.1 checked0229.2.2.2
    (power_identity10 plusWeights0229) (power_identity10 minusWeights0229) g hg hmax

def envelope0229 : Envelope := ⟨coefficients0229, upper0229, bound0229⟩

def coefficients0230 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/1024), (-15/1024), (-585/16384), (-525/32768)]

def upper0230 : ℚ := (21609/13107200000000)

def plusWeights0230 : Fin 11 → ℚ := ![(21609/13107200000000), (21609/1310720000000), (194481/2621440000000), (64827/327680000000), (453789/1310720000000), (1361367/3276800000000), (453789/1310720000000), (64347/327680000000), (182577/2621440000000), (77091/6553600000000), 0]

def minusWeights0230 : Fin 11 → ℚ := ![(21609/13107200000000), (21609/1310720000000), (194481/2621440000000), (64827/327680000000), (453789/1310720000000), (1361367/3276800000000), (453789/1310720000000), (65307/327680000000), (41277/524288000000), (138999/6553600000000), (21609/6553600000000)]

theorem checked0230 :
    (∀ i, 0 ≤ plusWeights0230 i) ∧
    (∀ i, 0 ≤ minusWeights0230 i) ∧
    (∀ i, plusCoefficients coefficients0230 upper0230 i = powerCoefficients10 plusWeights0230 i) ∧
    (∀ i, minusCoefficients coefficients0230 upper0230 i = powerCoefficients10 minusWeights0230 i) := by
  decide +kernel

theorem bound0230 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0230 g| ≤ (upper0230 : ℝ) :=
  abs_of_coefficients coefficients0230 upper0230 powerCoefficients10 plusWeights0230 minusWeights0230
    checked0230.1 checked0230.2.1 checked0230.2.2.1 checked0230.2.2.2
    (power_identity10 plusWeights0230) (power_identity10 minusWeights0230) g hg hmax

def envelope0230 : Envelope := ⟨coefficients0230, upper0230, bound0230⟩

def coefficients0231 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/1024), (-15/1024), (-5/512), (-25/8192)]

def upper0231 : ℚ := (5313/3276800000000)

def plusWeights0231 : Fin 11 → ℚ := ![(5313/3276800000000), (5313/327680000000), (47817/655360000000), (15939/81920000000), (111573/327680000000), (334719/819200000000), (111573/327680000000), (15819/81920000000), (44841/655360000000), (18869/1638400000000), 0]

def minusWeights0231 : Fin 11 → ℚ := ![(5313/3276800000000), (5313/327680000000), (47817/655360000000), (15939/81920000000), (111573/327680000000), (334719/819200000000), (111573/327680000000), (16059/81920000000), (50793/655360000000), (34261/1638400000000), (5313/1638400000000)]

theorem checked0231 :
    (∀ i, 0 ≤ plusWeights0231 i) ∧
    (∀ i, 0 ≤ minusWeights0231 i) ∧
    (∀ i, plusCoefficients coefficients0231 upper0231 i = powerCoefficients10 plusWeights0231 i) ∧
    (∀ i, minusCoefficients coefficients0231 upper0231 i = powerCoefficients10 minusWeights0231 i) := by
  decide +kernel

theorem bound0231 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0231 g| ≤ (upper0231 : ℝ) :=
  abs_of_coefficients coefficients0231 upper0231 powerCoefficients10 plusWeights0231 minusWeights0231
    checked0231.1 checked0231.2.1 checked0231.2.2.1 checked0231.2.2.2
    (power_identity10 plusWeights0231) (power_identity10 minusWeights0231) g hg hmax

def envelope0231 : Envelope := ⟨coefficients0231, upper0231, bound0231⟩

def coefficients0232 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/1024), (-15/1024), (-135/16384), (-75/32768)]

def upper0232 : ℚ := (21231/13107200000000)

def plusWeights0232 : Fin 11 → ℚ := ![(21231/13107200000000), (21231/1310720000000), (191079/2621440000000), (63693/327680000000), (445851/1310720000000), (1337553/3276800000000), (445851/1310720000000), (63213/327680000000), (7167/104857600000), (75381/6553600000000), 0]

def minusWeights0232 : Fin 11 → ℚ := ![(21231/13107200000000), (21231/1310720000000), (191079/2621440000000), (63693/327680000000), (445851/1310720000000), (1337553/3276800000000), (445851/1310720000000), (64173/327680000000), (202983/2621440000000), (136929/6553600000000), (21231/6553600000000)]

theorem checked0232 :
    (∀ i, 0 ≤ plusWeights0232 i) ∧
    (∀ i, 0 ≤ minusWeights0232 i) ∧
    (∀ i, plusCoefficients coefficients0232 upper0232 i = powerCoefficients10 plusWeights0232 i) ∧
    (∀ i, minusCoefficients coefficients0232 upper0232 i = powerCoefficients10 minusWeights0232 i) := by
  decide +kernel

theorem bound0232 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0232 g| ≤ (upper0232 : ℝ) :=
  abs_of_coefficients coefficients0232 upper0232 powerCoefficients10 plusWeights0232 minusWeights0232
    checked0232.1 checked0232.2.1 checked0232.2.2.1 checked0232.2.2.2
    (power_identity10 plusWeights0232) (power_identity10 minusWeights0232) g hg hmax

def envelope0232 : Envelope := ⟨coefficients0232, upper0232, bound0232⟩

def coefficients0233 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/1024), (405/16384), (825/32768), (3075/262144)]

def upper0233 : ℚ := (124917/104857600000000)

def plusWeights0233 : Fin 11 → ℚ := ![(124917/104857600000000), (124917/10485760000000), (1124253/20971520000000), (374751/2621440000000), (2623257/10485760000000), (7869771/26214400000000), (2623257/10485760000000), (370911/2621440000000), (1037277/20971520000000), (16857/2097152000000), 0]

def minusWeights0233 : Fin 11 → ℚ := ![(124917/104857600000000), (124917/10485760000000), (1124253/20971520000000), (374751/2621440000000), (2623257/10485760000000), (7869771/26214400000000), (2623257/10485760000000), (378591/2621440000000), (1211229/20971520000000), (165549/10485760000000), (124917/52428800000000)]

theorem checked0233 :
    (∀ i, 0 ≤ plusWeights0233 i) ∧
    (∀ i, 0 ≤ minusWeights0233 i) ∧
    (∀ i, plusCoefficients coefficients0233 upper0233 i = powerCoefficients10 plusWeights0233 i) ∧
    (∀ i, minusCoefficients coefficients0233 upper0233 i = powerCoefficients10 minusWeights0233 i) := by
  decide +kernel

theorem bound0233 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0233 g| ≤ (upper0233 : ℝ) :=
  abs_of_coefficients coefficients0233 upper0233 powerCoefficients10 plusWeights0233 minusWeights0233
    checked0233.1 checked0233.2.1 checked0233.2.2.1 checked0233.2.2.2
    (power_identity10 plusWeights0233) (power_identity10 minusWeights0233) g hg hmax

def envelope0233 : Envelope := ⟨coefficients0233, upper0233, bound0233⟩

def coefficients0234 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-213/4096), (-387/16384)]

def upper0234 : ℚ := (251307/163840000000000)

def plusWeights0234 : Fin 11 → ℚ := ![(251307/163840000000000), (251307/16384000000000), (2261763/32768000000000), (753921/4096000000000), (5277447/16384000000000), (15832341/40960000000000), (5277447/16384000000000), (748521/4096000000000), (2126883/32768000000000), (1443/131072000000), 0]

def minusWeights0234 : Fin 11 → ℚ := ![(251307/163840000000000), (251307/16384000000000), (2261763/32768000000000), (753921/4096000000000), (5277447/16384000000000), (15832341/40960000000000), (5277447/16384000000000), (759321/4096000000000), (2396643/32768000000000), (322239/16384000000000), (251307/81920000000000)]

theorem checked0234 :
    (∀ i, 0 ≤ plusWeights0234 i) ∧
    (∀ i, 0 ≤ minusWeights0234 i) ∧
    (∀ i, plusCoefficients coefficients0234 upper0234 i = powerCoefficients10 plusWeights0234 i) ∧
    (∀ i, minusCoefficients coefficients0234 upper0234 i = powerCoefficients10 minusWeights0234 i) := by
  decide +kernel

theorem bound0234 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0234 g| ≤ (upper0234 : ℝ) :=
  abs_of_coefficients coefficients0234 upper0234 powerCoefficients10 plusWeights0234 minusWeights0234
    checked0234.1 checked0234.2.1 checked0234.2.2.1 checked0234.2.2.2
    (power_identity10 plusWeights0234) (power_identity10 minusWeights0234) g hg hmax

def envelope0234 : Envelope := ⟨coefficients0234, upper0234, bound0234⟩

def coefficients0235 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-351/8192), (-39/2048)]

def upper0235 : ℚ := (62433/40960000000000)

def plusWeights0235 : Fin 11 → ℚ := ![(62433/40960000000000), (62433/4096000000000), (561897/8192000000000), (187299/1024000000000), (1311093/4096000000000), (3933279/10240000000000), (1311093/4096000000000), (185949/1024000000000), (528177/8192000000000), (3579/327680000000), 0]

def minusWeights0235 : Fin 11 → ℚ := ![(62433/40960000000000), (62433/4096000000000), (561897/8192000000000), (187299/1024000000000), (1311093/4096000000000), (3933279/10240000000000), (1311093/4096000000000), (188649/1024000000000), (595617/8192000000000), (160257/8192000000000), (62433/20480000000000)]

theorem checked0235 :
    (∀ i, 0 ≤ plusWeights0235 i) ∧
    (∀ i, 0 ≤ minusWeights0235 i) ∧
    (∀ i, plusCoefficients coefficients0235 upper0235 i = powerCoefficients10 plusWeights0235 i) ∧
    (∀ i, minusCoefficients coefficients0235 upper0235 i = powerCoefficients10 minusWeights0235 i) := by
  decide +kernel

theorem bound0235 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0235 g| ≤ (upper0235 : ℝ) :=
  abs_of_coefficients coefficients0235 upper0235 powerCoefficients10 plusWeights0235 minusWeights0235
    checked0235.1 checked0235.2.1 checked0235.2.2.1 checked0235.2.2.2
    (power_identity10 plusWeights0235) (power_identity10 minusWeights0235) g hg hmax

def envelope0235 : Envelope := ⟨coefficients0235, upper0235, bound0235⟩

def coefficients0236 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-627/16384), (-549/32768)]

def upper0236 : ℚ := (497889/327680000000000)

def plusWeights0236 : Fin 11 → ℚ := ![(497889/327680000000000), (497889/32768000000000), (4481001/65536000000000), (1493667/8192000000000), (10455669/32768000000000), (31367007/81920000000000), (10455669/32768000000000), (1482867/8192000000000), (4211241/65536000000000), (14259/1310720000000), 0]

def minusWeights0236 : Fin 11 → ℚ := ![(497889/327680000000000), (497889/32768000000000), (4481001/65536000000000), (1493667/8192000000000), (10455669/32768000000000), (31367007/81920000000000), (10455669/32768000000000), (1504467/8192000000000), (4750761/65536000000000), (639303/32768000000000), (497889/163840000000000)]

theorem checked0236 :
    (∀ i, 0 ≤ plusWeights0236 i) ∧
    (∀ i, 0 ≤ minusWeights0236 i) ∧
    (∀ i, plusCoefficients coefficients0236 upper0236 i = powerCoefficients10 plusWeights0236 i) ∧
    (∀ i, minusCoefficients coefficients0236 upper0236 i = powerCoefficients10 minusWeights0236 i) := by
  decide +kernel

theorem bound0236 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0236 g| ≤ (upper0236 : ℝ) :=
  abs_of_coefficients coefficients0236 upper0236 powerCoefficients10 plusWeights0236 minusWeights0236
    checked0236.1 checked0236.2.1 checked0236.2.2.1 checked0236.2.2.2
    (power_identity10 plusWeights0236) (power_identity10 minusWeights0236) g hg hmax

def envelope0236 : Envelope := ⟨coefficients0236, upper0236, bound0236⟩

def coefficients0237 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-477/16384), (-399/32768)]

def upper0237 : ℚ := (494739/327680000000000)

def plusWeights0237 : Fin 11 → ℚ := ![(494739/327680000000000), (494739/32768000000000), (4452651/65536000000000), (1484217/8192000000000), (10389519/32768000000000), (31168557/81920000000000), (10389519/32768000000000), (1473417/8192000000000), (4182891/65536000000000), (2829/262144000000), 0]

def minusWeights0237 : Fin 11 → ℚ := ![(494739/327680000000000), (494739/32768000000000), (4452651/65536000000000), (1484217/8192000000000), (10389519/32768000000000), (31168557/81920000000000), (10389519/32768000000000), (1495017/8192000000000), (4722411/65536000000000), (635853/32768000000000), (494739/163840000000000)]

theorem checked0237 :
    (∀ i, 0 ≤ plusWeights0237 i) ∧
    (∀ i, 0 ≤ minusWeights0237 i) ∧
    (∀ i, plusCoefficients coefficients0237 upper0237 i = powerCoefficients10 plusWeights0237 i) ∧
    (∀ i, minusCoefficients coefficients0237 upper0237 i = powerCoefficients10 minusWeights0237 i) := by
  decide +kernel

theorem bound0237 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0237 g| ≤ (upper0237 : ℝ) :=
  abs_of_coefficients coefficients0237 upper0237 powerCoefficients10 plusWeights0237 minusWeights0237
    checked0237.1 checked0237.2.1 checked0237.2.2.1 checked0237.2.2.2
    (power_identity10 plusWeights0237) (power_identity10 minusWeights0237) g hg hmax

def envelope0237 : Envelope := ⟨coefficients0237, upper0237, bound0237⟩

def coefficients0238 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-201/8192), (-81/8192)]

def upper0238 : ℚ := (123291/81920000000000)

def plusWeights0238 : Fin 11 → ℚ := ![(123291/81920000000000), (123291/8192000000000), (1109619/16384000000000), (369873/2048000000000), (2589111/8192000000000), (7767333/20480000000000), (2589111/8192000000000), (367173/2048000000000), (1042179/16384000000000), (1761/163840000000), 0]

def minusWeights0238 : Fin 11 → ℚ := ![(123291/81920000000000), (123291/8192000000000), (1109619/16384000000000), (369873/2048000000000), (2589111/8192000000000), (7767333/20480000000000), (2589111/8192000000000), (372573/2048000000000), (1177059/16384000000000), (39633/2048000000000), (123291/40960000000000)]

theorem checked0238 :
    (∀ i, 0 ≤ plusWeights0238 i) ∧
    (∀ i, 0 ≤ minusWeights0238 i) ∧
    (∀ i, plusCoefficients coefficients0238 upper0238 i = powerCoefficients10 plusWeights0238 i) ∧
    (∀ i, minusCoefficients coefficients0238 upper0238 i = powerCoefficients10 minusWeights0238 i) := by
  decide +kernel

theorem bound0238 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0238 g| ≤ (upper0238 : ℝ) :=
  abs_of_coefficients coefficients0238 upper0238 powerCoefficients10 plusWeights0238 minusWeights0238
    checked0238.1 checked0238.2.1 checked0238.2.2.1 checked0238.2.2.2
    (power_identity10 plusWeights0238) (power_identity10 minusWeights0238) g hg hmax

def envelope0238 : Envelope := ⟨coefficients0238, upper0238, bound0238⟩

def coefficients0239 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-327/16384), (-249/32768)]

def upper0239 : ℚ := (491589/327680000000000)

def plusWeights0239 : Fin 11 → ℚ := ![(491589/327680000000000), (491589/32768000000000), (4424301/65536000000000), (1474767/8192000000000), (10323369/32768000000000), (30970107/81920000000000), (10323369/32768000000000), (1463967/8192000000000), (4154541/65536000000000), (14031/1310720000000), 0]

def minusWeights0239 : Fin 11 → ℚ := ![(491589/327680000000000), (491589/32768000000000), (4424301/65536000000000), (1474767/8192000000000), (10323369/32768000000000), (30970107/81920000000000), (10323369/32768000000000), (1485567/8192000000000), (4694061/65536000000000), (632403/32768000000000), (491589/163840000000000)]

theorem checked0239 :
    (∀ i, 0 ≤ plusWeights0239 i) ∧
    (∀ i, 0 ≤ minusWeights0239 i) ∧
    (∀ i, plusCoefficients coefficients0239 upper0239 i = powerCoefficients10 plusWeights0239 i) ∧
    (∀ i, minusCoefficients coefficients0239 upper0239 i = powerCoefficients10 minusWeights0239 i) := by
  decide +kernel

theorem bound0239 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0239 g| ≤ (upper0239 : ℝ) :=
  abs_of_coefficients coefficients0239 upper0239 powerCoefficients10 plusWeights0239 minusWeights0239
    checked0239.1 checked0239.2.1 checked0239.2.2.1 checked0239.2.2.2
    (power_identity10 plusWeights0239) (power_identity10 minusWeights0239) g hg hmax

def envelope0239 : Envelope := ⟨coefficients0239, upper0239, bound0239⟩

def coefficients0240 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-105/8192), (-15/4096), (-615/16384), (-75/4096)]

def upper0240 : ℚ := (4449/3276800000000)

def plusWeights0240 : Fin 11 → ℚ := ![(4449/3276800000000), (4449/327680000000), (40041/655360000000), (13347/81920000000), (93429/327680000000), (280287/819200000000), (93429/327680000000), (6621/40960000000), (37497/655360000000), (31527/3276800000000), 0]

def minusWeights0240 : Fin 11 → ℚ := ![(4449/3276800000000), (4449/327680000000), (40041/655360000000), (13347/81920000000), (93429/327680000000), (280287/819200000000), (93429/327680000000), (3363/20480000000), (8517/131072000000), (57453/3276800000000), (4449/1638400000000)]

theorem checked0240 :
    (∀ i, 0 ≤ plusWeights0240 i) ∧
    (∀ i, 0 ≤ minusWeights0240 i) ∧
    (∀ i, plusCoefficients coefficients0240 upper0240 i = powerCoefficients10 plusWeights0240 i) ∧
    (∀ i, minusCoefficients coefficients0240 upper0240 i = powerCoefficients10 minusWeights0240 i) := by
  decide +kernel

theorem bound0240 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0240 g| ≤ (upper0240 : ℝ) :=
  abs_of_coefficients coefficients0240 upper0240 powerCoefficients10 plusWeights0240 minusWeights0240
    checked0240.1 checked0240.2.1 checked0240.2.2.1 checked0240.2.2.2
    (power_identity10 plusWeights0240) (power_identity10 minusWeights0240) g hg hmax

def envelope0240 : Envelope := ⟨coefficients0240, upper0240, bound0240⟩

def coefficients0241 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-105/8192), (-15/4096), (-555/32768), (-525/65536)]

def upper0241 : ℚ := (1401/1048576000000)

def plusWeights0241 : Fin 11 → ℚ := ![(1401/1048576000000), (1401/104857600000), (12609/209715200000), (4203/26214400000), (29421/104857600000), (88263/262144000000), (29421/104857600000), (20847/131072000000), (294873/5242880000000), (123543/13107200000000), 0]

def minusWeights0241 : Fin 11 → ℚ := ![(1401/1048576000000), (1401/104857600000), (12609/209715200000), (4203/26214400000), (29421/104857600000), (88263/262144000000), (29421/104857600000), (21183/131072000000), (335577/5242880000000), (226707/13107200000000), (1401/524288000000)]

theorem checked0241 :
    (∀ i, 0 ≤ plusWeights0241 i) ∧
    (∀ i, 0 ≤ minusWeights0241 i) ∧
    (∀ i, plusCoefficients coefficients0241 upper0241 i = powerCoefficients10 plusWeights0241 i) ∧
    (∀ i, minusCoefficients coefficients0241 upper0241 i = powerCoefficients10 minusWeights0241 i) := by
  decide +kernel

theorem bound0241 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0241 g| ≤ (upper0241 : ℝ) :=
  abs_of_coefficients coefficients0241 upper0241 powerCoefficients10 plusWeights0241 minusWeights0241
    checked0241.1 checked0241.2.1 checked0241.2.2.1 checked0241.2.2.2
    (power_identity10 plusWeights0241) (power_identity10 minusWeights0241) g hg hmax

def envelope0241 : Envelope := ⟨coefficients0241, upper0241, bound0241⟩

def coefficients0242 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-105/8192), (-15/4096), (-215/16384), (-25/4096)]

def upper0242 : ℚ := (873/655360000000)

def plusWeights0242 : Fin 11 → ℚ := ![(873/655360000000), (873/65536000000), (7857/131072000000), (2619/16384000000), (18333/65536000000), (54999/163840000000), (18333/65536000000), (1299/8192000000), (36741/655360000000), (30767/3276800000000), 0]

def minusWeights0242 : Fin 11 → ℚ := ![(873/655360000000), (873/65536000000), (7857/131072000000), (2619/16384000000), (18333/65536000000), (54999/163840000000), (18333/65536000000), (33/204800000), (41829/655360000000), (56533/3276800000000), (873/327680000000)]

theorem checked0242 :
    (∀ i, 0 ≤ plusWeights0242 i) ∧
    (∀ i, 0 ≤ minusWeights0242 i) ∧
    (∀ i, plusCoefficients coefficients0242 upper0242 i = powerCoefficients10 plusWeights0242 i) ∧
    (∀ i, minusCoefficients coefficients0242 upper0242 i = powerCoefficients10 minusWeights0242 i) := by
  decide +kernel

theorem bound0242 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0242 g| ≤ (upper0242 : ℝ) :=
  abs_of_coefficients coefficients0242 upper0242 powerCoefficients10 plusWeights0242 minusWeights0242
    checked0242.1 checked0242.2.1 checked0242.2.2.1 checked0242.2.2.2
    (power_identity10 plusWeights0242) (power_identity10 minusWeights0242) g hg hmax

def envelope0242 : Envelope := ⟨coefficients0242, upper0242, bound0242⟩

def coefficients0243 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-105/8192), (-15/4096), (-165/16384), (-75/16384)]

def upper0243 : ℚ := (8709/6553600000000)

def plusWeights0243 : Fin 11 → ℚ := ![(8709/6553600000000), (8709/655360000000), (78381/1310720000000), (26127/163840000000), (182889/655360000000), (548667/1638400000000), (182889/655360000000), (25917/163840000000), (73293/1310720000000), (1917/204800000000), 0]

def minusWeights0243 : Fin 11 → ℚ := ![(8709/6553600000000), (8709/655360000000), (78381/1310720000000), (26127/163840000000), (182889/655360000000), (548667/1638400000000), (182889/655360000000), (26337/163840000000), (83469/1310720000000), (28209/1638400000000), (8709/3276800000000)]

theorem checked0243 :
    (∀ i, 0 ≤ plusWeights0243 i) ∧
    (∀ i, 0 ≤ minusWeights0243 i) ∧
    (∀ i, plusCoefficients coefficients0243 upper0243 i = powerCoefficients10 plusWeights0243 i) ∧
    (∀ i, minusCoefficients coefficients0243 upper0243 i = powerCoefficients10 minusWeights0243 i) := by
  decide +kernel

theorem bound0243 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0243 g| ≤ (upper0243 : ℝ) :=
  abs_of_coefficients coefficients0243 upper0243 powerCoefficients10 plusWeights0243 minusWeights0243
    checked0243.1 checked0243.2.1 checked0243.2.2.1 checked0243.2.2.2
    (power_identity10 plusWeights0243) (power_identity10 minusWeights0243) g hg hmax

def envelope0243 : Envelope := ⟨coefficients0243, upper0243, bound0243⟩

def coefficients0244 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-105/8192), (-15/4096), (-305/32768), (-275/65536)]

def upper0244 : ℚ := (6963/5242880000000)

def plusWeights0244 : Fin 11 → ℚ := ![(6963/5242880000000), (6963/524288000000), (62667/1048576000000), (20889/131072000000), (146223/524288000000), (438669/1310720000000), (146223/524288000000), (20721/131072000000), (292983/5242880000000), (122593/13107200000000), 0]

def minusWeights0244 : Fin 11 → ℚ := ![(6963/5242880000000), (6963/524288000000), (62667/1048576000000), (20889/131072000000), (146223/524288000000), (438669/1310720000000), (146223/524288000000), (21057/131072000000), (333687/5242880000000), (225557/13107200000000), (6963/2621440000000)]

theorem checked0244 :
    (∀ i, 0 ≤ plusWeights0244 i) ∧
    (∀ i, 0 ≤ minusWeights0244 i) ∧
    (∀ i, plusCoefficients coefficients0244 upper0244 i = powerCoefficients10 plusWeights0244 i) ∧
    (∀ i, minusCoefficients coefficients0244 upper0244 i = powerCoefficients10 minusWeights0244 i) := by
  decide +kernel

theorem bound0244 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0244 g| ≤ (upper0244 : ℝ) :=
  abs_of_coefficients coefficients0244 upper0244 powerCoefficients10 plusWeights0244 minusWeights0244
    checked0244.1 checked0244.2.1 checked0244.2.2.1 checked0244.2.2.2
    (power_identity10 plusWeights0244) (power_identity10 minusWeights0244) g hg hmax

def envelope0244 : Envelope := ⟨coefficients0244, upper0244, bound0244⟩

def coefficients0245 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-95/8192), (-5/2048), (-445/32768), (-425/65536)]

def upper0245 : ℚ := (31413/26214400000000)

def plusWeights0245 : Fin 11 → ℚ := ![(31413/26214400000000), (31413/2621440000000), (282717/5242880000000), (94239/655360000000), (659673/2621440000000), (1979019/6553600000000), (659673/2621440000000), (93479/655360000000), (264349/5242880000000), (110647/13107200000000), 0]

def minusWeights0245 : Fin 11 → ℚ := ![(31413/26214400000000), (31413/2621440000000), (282717/5242880000000), (94239/655360000000), (659673/2621440000000), (1979019/6553600000000), (659673/2621440000000), (94999/655360000000), (60217/1048576000000), (203483/13107200000000), (31413/13107200000000)]

theorem checked0245 :
    (∀ i, 0 ≤ plusWeights0245 i) ∧
    (∀ i, 0 ≤ minusWeights0245 i) ∧
    (∀ i, plusCoefficients coefficients0245 upper0245 i = powerCoefficients10 plusWeights0245 i) ∧
    (∀ i, minusCoefficients coefficients0245 upper0245 i = powerCoefficients10 minusWeights0245 i) := by
  decide +kernel

theorem bound0245 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0245 g| ≤ (upper0245 : ℝ) :=
  abs_of_coefficients coefficients0245 upper0245 powerCoefficients10 plusWeights0245 minusWeights0245
    checked0245.1 checked0245.2.1 checked0245.2.2.1 checked0245.2.2.2
    (power_identity10 plusWeights0245) (power_identity10 minusWeights0245) g hg hmax

def envelope0245 : Envelope := ⟨coefficients0245, upper0245, bound0245⟩

def coefficients0246 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-95/8192), (65/4096), (-105/8192), (-275/32768)]

def upper0246 : ℚ := (13299/13107200000000)

def plusWeights0246 : Fin 11 → ℚ := ![(13299/13107200000000), (13299/1310720000000), (119691/2621440000000), (39897/327680000000), (279279/1310720000000), (837837/3276800000000), (279279/1310720000000), (39517/327680000000), (110987/2621440000000), (45691/6553600000000), 0]

def minusWeights0246 : Fin 11 → ℚ := ![(13299/13107200000000), (13299/1310720000000), (119691/2621440000000), (39897/327680000000), (279279/1310720000000), (837837/3276800000000), (279279/1310720000000), (40277/327680000000), (25679/524288000000), (87299/6553600000000), (13299/6553600000000)]

theorem checked0246 :
    (∀ i, 0 ≤ plusWeights0246 i) ∧
    (∀ i, 0 ≤ minusWeights0246 i) ∧
    (∀ i, plusCoefficients coefficients0246 upper0246 i = powerCoefficients10 plusWeights0246 i) ∧
    (∀ i, minusCoefficients coefficients0246 upper0246 i = powerCoefficients10 minusWeights0246 i) := by
  decide +kernel

theorem bound0246 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0246 g| ≤ (upper0246 : ℝ) :=
  abs_of_coefficients coefficients0246 upper0246 powerCoefficients10 plusWeights0246 minusWeights0246
    checked0246.1 checked0246.2.1 checked0246.2.2.1 checked0246.2.2.2
    (power_identity10 plusWeights0246) (power_identity10 minusWeights0246) g hg hmax

def envelope0246 : Envelope := ⟨coefficients0246, upper0246, bound0246⟩

def coefficients0247 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-95/8192), (65/4096), (-135/16384), (-25/4096)]

def upper0247 : ℚ := (3309/3276800000000)

def plusWeights0247 : Fin 11 → ℚ := ![(3309/3276800000000), (3309/327680000000), (29781/655360000000), (9927/81920000000), (69489/327680000000), (208467/819200000000), (69489/327680000000), (1229/10240000000), (5521/131072000000), (22703/3276800000000), 0]

def minusWeights0247 : Fin 11 → ℚ := ![(3309/3276800000000), (3309/327680000000), (29781/655360000000), (9927/81920000000), (69489/327680000000), (208467/819200000000), (69489/327680000000), (5011/40960000000), (31957/655360000000), (43477/3276800000000), (3309/1638400000000)]

theorem checked0247 :
    (∀ i, 0 ≤ plusWeights0247 i) ∧
    (∀ i, 0 ≤ minusWeights0247 i) ∧
    (∀ i, plusCoefficients coefficients0247 upper0247 i = powerCoefficients10 plusWeights0247 i) ∧
    (∀ i, minusCoefficients coefficients0247 upper0247 i = powerCoefficients10 minusWeights0247 i) := by
  decide +kernel

theorem bound0247 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0247 g| ≤ (upper0247 : ℝ) :=
  abs_of_coefficients coefficients0247 upper0247 powerCoefficients10 plusWeights0247 minusWeights0247
    checked0247.1 checked0247.2.1 checked0247.2.2.1 checked0247.2.2.2
    (power_identity10 plusWeights0247) (power_identity10 minusWeights0247) g hg hmax

def envelope0247 : Envelope := ⟨coefficients0247, upper0247, bound0247⟩

def coefficients0248 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/512), (-5/512), (-135/4096), (-125/8192)]

def upper0248 : ℚ := (3633/3276800000000)

def plusWeights0248 : Fin 11 → ℚ := ![(3633/3276800000000), (3633/327680000000), (32697/655360000000), (10899/81920000000), (76293/327680000000), (228879/819200000000), (76293/327680000000), (10819/81920000000), (30713/655360000000), (12991/1638400000000), 0]

def minusWeights0248 : Fin 11 → ℚ := ![(3633/3276800000000), (3633/327680000000), (32697/655360000000), (10899/81920000000), (76293/327680000000), (228879/819200000000), (76293/327680000000), (10979/81920000000), (34681/655360000000), (23339/1638400000000), (3633/1638400000000)]

theorem checked0248 :
    (∀ i, 0 ≤ plusWeights0248 i) ∧
    (∀ i, 0 ≤ minusWeights0248 i) ∧
    (∀ i, plusCoefficients coefficients0248 upper0248 i = powerCoefficients10 plusWeights0248 i) ∧
    (∀ i, minusCoefficients coefficients0248 upper0248 i = powerCoefficients10 minusWeights0248 i) := by
  decide +kernel

theorem bound0248 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0248 g| ≤ (upper0248 : ℝ) :=
  abs_of_coefficients coefficients0248 upper0248 powerCoefficients10 plusWeights0248 minusWeights0248
    checked0248.1 checked0248.2.1 checked0248.2.2.1 checked0248.2.2.2
    (power_identity10 plusWeights0248) (power_identity10 minusWeights0248) g hg hmax

def envelope0248 : Envelope := ⟨coefficients0248, upper0248, bound0248⟩

def coefficients0249 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/512), (-5/512), (-195/8192), (-175/16384)]

def upper0249 : ℚ := (7203/6553600000000)

def plusWeights0249 : Fin 11 → ℚ := ![(7203/6553600000000), (7203/655360000000), (64827/1310720000000), (21609/163840000000), (151263/655360000000), (453789/1638400000000), (151263/655360000000), (21449/163840000000), (60859/1310720000000), (25697/3276800000000), 0]

def minusWeights0249 : Fin 11 → ℚ := ![(7203/6553600000000), (7203/655360000000), (64827/1310720000000), (21609/163840000000), (151263/655360000000), (453789/1638400000000), (151263/655360000000), (21769/163840000000), (13759/262144000000), (46333/3276800000000), (7203/3276800000000)]

theorem checked0249 :
    (∀ i, 0 ≤ plusWeights0249 i) ∧
    (∀ i, 0 ≤ minusWeights0249 i) ∧
    (∀ i, plusCoefficients coefficients0249 upper0249 i = powerCoefficients10 plusWeights0249 i) ∧
    (∀ i, minusCoefficients coefficients0249 upper0249 i = powerCoefficients10 minusWeights0249 i) := by
  decide +kernel

theorem bound0249 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0249 g| ≤ (upper0249 : ℝ) :=
  abs_of_coefficients coefficients0249 upper0249 powerCoefficients10 plusWeights0249 minusWeights0249
    checked0249.1 checked0249.2.1 checked0249.2.2.1 checked0249.2.2.2
    (power_identity10 plusWeights0249) (power_identity10 minusWeights0249) g hg hmax

def envelope0249 : Envelope := ⟨coefficients0249, upper0249, bound0249⟩

def coefficients0250 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/512), (-5/512), (-85/4096), (-75/8192)]

def upper0250 : ℚ := (3591/3276800000000)

def plusWeights0250 : Fin 11 → ℚ := ![(3591/3276800000000), (3591/327680000000), (32319/655360000000), (10773/81920000000), (75411/327680000000), (226233/819200000000), (75411/327680000000), (10693/81920000000), (6067/131072000000), (12801/1638400000000), 0]

def minusWeights0250 : Fin 11 → ℚ := ![(3591/3276800000000), (3591/327680000000), (32319/655360000000), (10773/81920000000), (75411/327680000000), (226233/819200000000), (75411/327680000000), (10853/81920000000), (34303/655360000000), (23109/1638400000000), (3591/1638400000000)]

theorem checked0250 :
    (∀ i, 0 ≤ plusWeights0250 i) ∧
    (∀ i, 0 ≤ minusWeights0250 i) ∧
    (∀ i, plusCoefficients coefficients0250 upper0250 i = powerCoefficients10 plusWeights0250 i) ∧
    (∀ i, minusCoefficients coefficients0250 upper0250 i = powerCoefficients10 minusWeights0250 i) := by
  decide +kernel

theorem bound0250 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0250 g| ≤ (upper0250 : ℝ) :=
  abs_of_coefficients coefficients0250 upper0250 powerCoefficients10 plusWeights0250 minusWeights0250
    checked0250.1 checked0250.2.1 checked0250.2.2.1 checked0250.2.2.2
    (power_identity10 plusWeights0250) (power_identity10 minusWeights0250) g hg hmax

def envelope0250 : Envelope := ⟨coefficients0250, upper0250, bound0250⟩

def coefficients0251 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/512), (-5/512), (-145/8192), (-125/16384)]

def upper0251 : ℚ := (7161/6553600000000)

def plusWeights0251 : Fin 11 → ℚ := ![(7161/6553600000000), (7161/655360000000), (64449/1310720000000), (21483/163840000000), (150381/655360000000), (451143/1638400000000), (150381/655360000000), (21323/163840000000), (60481/1310720000000), (25507/3276800000000), 0]

def minusWeights0251 : Fin 11 → ℚ := ![(7161/6553600000000), (7161/655360000000), (64449/1310720000000), (21483/163840000000), (150381/655360000000), (451143/1638400000000), (150381/655360000000), (21643/163840000000), (68417/1310720000000), (46103/3276800000000), (7161/3276800000000)]

theorem checked0251 :
    (∀ i, 0 ≤ plusWeights0251 i) ∧
    (∀ i, 0 ≤ minusWeights0251 i) ∧
    (∀ i, plusCoefficients coefficients0251 upper0251 i = powerCoefficients10 plusWeights0251 i) ∧
    (∀ i, minusCoefficients coefficients0251 upper0251 i = powerCoefficients10 minusWeights0251 i) := by
  decide +kernel

theorem bound0251 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0251 g| ≤ (upper0251 : ℝ) :=
  abs_of_coefficients coefficients0251 upper0251 powerCoefficients10 plusWeights0251 minusWeights0251
    checked0251.1 checked0251.2.1 checked0251.2.2.1 checked0251.2.2.2
    (power_identity10 plusWeights0251) (power_identity10 minusWeights0251) g hg hmax

def envelope0251 : Envelope := ⟨coefficients0251, upper0251, bound0251⟩

def coefficients0252 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/512), (-5/512), (-35/4096), (-25/8192)]

def upper0252 : ℚ := (3549/3276800000000)

def plusWeights0252 : Fin 11 → ℚ := ![(3549/3276800000000), (3549/327680000000), (31941/655360000000), (10647/81920000000), (74529/327680000000), (223587/819200000000), (74529/327680000000), (10567/81920000000), (29957/655360000000), (12611/1638400000000), 0]

def minusWeights0252 : Fin 11 → ℚ := ![(3549/3276800000000), (3549/327680000000), (31941/655360000000), (10647/81920000000), (74529/327680000000), (223587/819200000000), (74529/327680000000), (10727/81920000000), (1357/26214400000), (22879/1638400000000), (3549/1638400000000)]

theorem checked0252 :
    (∀ i, 0 ≤ plusWeights0252 i) ∧
    (∀ i, 0 ≤ minusWeights0252 i) ∧
    (∀ i, plusCoefficients coefficients0252 upper0252 i = powerCoefficients10 plusWeights0252 i) ∧
    (∀ i, minusCoefficients coefficients0252 upper0252 i = powerCoefficients10 minusWeights0252 i) := by
  decide +kernel

theorem bound0252 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0252 g| ≤ (upper0252 : ℝ) :=
  abs_of_coefficients coefficients0252 upper0252 powerCoefficients10 plusWeights0252 minusWeights0252
    checked0252.1 checked0252.2.1 checked0252.2.2.1 checked0252.2.2.2
    (power_identity10 plusWeights0252) (power_identity10 minusWeights0252) g hg hmax

def envelope0252 : Envelope := ⟨coefficients0252, upper0252, bound0252⟩

def coefficients0253 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/512), (-5/512), (-45/8192), (-25/16384)]

def upper0253 : ℚ := (7077/6553600000000)

def plusWeights0253 : Fin 11 → ℚ := ![(7077/6553600000000), (7077/655360000000), (63693/1310720000000), (21231/163840000000), (148617/655360000000), (445851/1638400000000), (148617/655360000000), (21071/163840000000), (2389/52428800000), (25127/3276800000000), 0]

def minusWeights0253 : Fin 11 → ℚ := ![(7077/6553600000000), (7077/655360000000), (63693/1310720000000), (21231/163840000000), (148617/655360000000), (445851/1638400000000), (148617/655360000000), (21391/163840000000), (67661/1310720000000), (45643/3276800000000), (7077/3276800000000)]

theorem checked0253 :
    (∀ i, 0 ≤ plusWeights0253 i) ∧
    (∀ i, 0 ≤ minusWeights0253 i) ∧
    (∀ i, plusCoefficients coefficients0253 upper0253 i = powerCoefficients10 plusWeights0253 i) ∧
    (∀ i, minusCoefficients coefficients0253 upper0253 i = powerCoefficients10 minusWeights0253 i) := by
  decide +kernel

theorem bound0253 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0253 g| ≤ (upper0253 : ℝ) :=
  abs_of_coefficients coefficients0253 upper0253 powerCoefficients10 plusWeights0253 minusWeights0253
    checked0253.1 checked0253.2.1 checked0253.2.2.1 checked0253.2.2.2
    (power_identity10 plusWeights0253) (power_identity10 minusWeights0253) g hg hmax

def envelope0253 : Envelope := ⟨coefficients0253, upper0253, bound0253⟩

def coefficients0254 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-19/2048), (-21/2048), (-329/16384), (-283/32768)]

def upper0254 : ℚ := (344463/327680000000000)

def plusWeights0254 : Fin 11 → ℚ := ![(344463/327680000000000), (344463/32768000000000), (3100167/65536000000000), (1033389/8192000000000), (7233723/32768000000000), (21701169/81920000000000), (7233723/32768000000000), (1025789/8192000000000), (2911047/65536000000000), (49177/6553600000000), 0]

def minusWeights0254 : Fin 11 → ℚ := ![(344463/327680000000000), (344463/32768000000000), (3100167/65536000000000), (1033389/8192000000000), (7233723/32768000000000), (21701169/81920000000000), (7233723/32768000000000), (1040989/8192000000000), (3289287/65536000000000), (443041/32768000000000), (344463/163840000000000)]

theorem checked0254 :
    (∀ i, 0 ≤ plusWeights0254 i) ∧
    (∀ i, 0 ≤ minusWeights0254 i) ∧
    (∀ i, plusCoefficients coefficients0254 upper0254 i = powerCoefficients10 plusWeights0254 i) ∧
    (∀ i, minusCoefficients coefficients0254 upper0254 i = powerCoefficients10 minusWeights0254 i) := by
  decide +kernel

theorem bound0254 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0254 g| ≤ (upper0254 : ℝ) :=
  abs_of_coefficients coefficients0254 upper0254 powerCoefficients10 plusWeights0254 minusWeights0254
    checked0254.1 checked0254.2.1 checked0254.2.2.1 checked0254.2.2.2
    (power_identity10 plusWeights0254) (power_identity10 minusWeights0254) g hg hmax

def envelope0254 : Envelope := ⟨coefficients0254, upper0254, bound0254⟩

def coefficients0255 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-19/2048), (-21/2048), (-179/16384), (-133/32768)]

def upper0255 : ℚ := (341313/327680000000000)

def plusWeights0255 : Fin 11 → ℚ := ![(341313/327680000000000), (341313/32768000000000), (3071817/65536000000000), (1023939/8192000000000), (7167573/32768000000000), (21502719/81920000000000), (7167573/32768000000000), (1016339/8192000000000), (2882697/65536000000000), (48607/6553600000000), 0]

def minusWeights0255 : Fin 11 → ℚ := ![(341313/327680000000000), (341313/32768000000000), (3071817/65536000000000), (1023939/8192000000000), (7167573/32768000000000), (21502719/81920000000000), (7167573/32768000000000), (1031539/8192000000000), (3260937/65536000000000), (439591/32768000000000), (341313/163840000000000)]

theorem checked0255 :
    (∀ i, 0 ≤ plusWeights0255 i) ∧
    (∀ i, 0 ≤ minusWeights0255 i) ∧
    (∀ i, plusCoefficients coefficients0255 upper0255 i = powerCoefficients10 plusWeights0255 i) ∧
    (∀ i, minusCoefficients coefficients0255 upper0255 i = powerCoefficients10 minusWeights0255 i) := by
  decide +kernel

theorem bound0255 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0255 g| ≤ (upper0255 : ℝ) :=
  abs_of_coefficients coefficients0255 upper0255 powerCoefficients10 plusWeights0255 minusWeights0255
    checked0255.1 checked0255.2.1 checked0255.2.2.1 checked0255.2.2.2
    (power_identity10 plusWeights0255) (power_identity10 minusWeights0255) g hg hmax

def envelope0255 : Envelope := ⟨coefficients0255, upper0255, bound0255⟩

end BilayerDressed.CubicQuarticEnvelopes

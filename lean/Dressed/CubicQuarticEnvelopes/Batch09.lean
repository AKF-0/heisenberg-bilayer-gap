import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0288 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-525/32768), (-525/65536), (-2625/524288)]

def upper0288 : ℚ := (7077/41943040000000)

def plusWeights0288 : Fin 11 → ℚ := ![(7077/41943040000000), (7077/4194304000000), (63693/8388608000000), (21231/1048576000000), (148617/4194304000000), (445851/10485760000000), (148617/4194304000000), (21231/1048576000000), (62349/8388608000000), (28497/20971520000000), 0]

def minusWeights0288 : Fin 11 → ℚ := ![(7077/41943040000000), (7077/4194304000000), (63693/8388608000000), (21231/1048576000000), (148617/4194304000000), (445851/10485760000000), (148617/4194304000000), (21231/1048576000000), (65037/8388608000000), (42273/20971520000000), (7077/20971520000000)]

theorem checked0288 :
    (∀ i, 0 ≤ plusWeights0288 i) ∧
    (∀ i, 0 ≤ minusWeights0288 i) ∧
    (∀ i, plusCoefficients coefficients0288 upper0288 i = powerCoefficients10 plusWeights0288 i) ∧
    (∀ i, minusCoefficients coefficients0288 upper0288 i = powerCoefficients10 minusWeights0288 i) := by
  decide +kernel

theorem bound0288 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0288 g| ≤ (upper0288 : ℝ) :=
  abs_of_coefficients coefficients0288 upper0288 powerCoefficients10 plusWeights0288 minusWeights0288
    checked0288.1 checked0288.2.1 checked0288.2.2.1 checked0288.2.2.2
    (power_identity10 plusWeights0288) (power_identity10 minusWeights0288) g hg hmax

def envelope0288 : Envelope := ⟨coefficients0288, upper0288, bound0288⟩

def coefficients0289 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-525/32768), (-525/65536), (375/524288)]

def upper0289 : ℚ := (7053/41943040000000)

def plusWeights0289 : Fin 11 → ℚ := ![(7053/41943040000000), (7053/4194304000000), (63477/8388608000000), (21159/1048576000000), (148113/4194304000000), (444339/10485760000000), (148113/4194304000000), (21159/1048576000000), (62133/8388608000000), (28377/20971520000000), 0]

def minusWeights0289 : Fin 11 → ℚ := ![(7053/41943040000000), (7053/4194304000000), (63477/8388608000000), (21159/1048576000000), (148113/4194304000000), (444339/10485760000000), (148113/4194304000000), (21159/1048576000000), (64821/8388608000000), (42153/20971520000000), (7053/20971520000000)]

theorem checked0289 :
    (∀ i, 0 ≤ plusWeights0289 i) ∧
    (∀ i, 0 ≤ minusWeights0289 i) ∧
    (∀ i, plusCoefficients coefficients0289 upper0289 i = powerCoefficients10 plusWeights0289 i) ∧
    (∀ i, minusCoefficients coefficients0289 upper0289 i = powerCoefficients10 minusWeights0289 i) := by
  decide +kernel

theorem bound0289 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0289 g| ≤ (upper0289 : ℝ) :=
  abs_of_coefficients coefficients0289 upper0289 powerCoefficients10 plusWeights0289 minusWeights0289
    checked0289.1 checked0289.2.1 checked0289.2.2.1 checked0289.2.2.2
    (power_identity10 plusWeights0289) (power_identity10 minusWeights0289) g hg hmax

def envelope0289 : Envelope := ⟨coefficients0289, upper0289, bound0289⟩

def coefficients0290 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-75/16384), (-75/32768), (-375/262144)]

def upper0290 : ℚ := (1011/20971520000000)

def plusWeights0290 : Fin 11 → ℚ := ![(1011/20971520000000), (1011/2097152000000), (9099/4194304000000), (3033/524288000000), (21231/2097152000000), (63693/5242880000000), (21231/2097152000000), (3033/524288000000), (8907/4194304000000), (4071/10485760000000), 0]

def minusWeights0290 : Fin 11 → ℚ := ![(1011/20971520000000), (1011/2097152000000), (9099/4194304000000), (3033/524288000000), (21231/2097152000000), (63693/5242880000000), (21231/2097152000000), (3033/524288000000), (9291/4194304000000), (6039/10485760000000), (1011/10485760000000)]

theorem checked0290 :
    (∀ i, 0 ≤ plusWeights0290 i) ∧
    (∀ i, 0 ≤ minusWeights0290 i) ∧
    (∀ i, plusCoefficients coefficients0290 upper0290 i = powerCoefficients10 plusWeights0290 i) ∧
    (∀ i, minusCoefficients coefficients0290 upper0290 i = powerCoefficients10 minusWeights0290 i) := by
  decide +kernel

theorem bound0290 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0290 g| ≤ (upper0290 : ℝ) :=
  abs_of_coefficients coefficients0290 upper0290 powerCoefficients10 plusWeights0290 minusWeights0290
    checked0290.1 checked0290.2.1 checked0290.2.2.1 checked0290.2.2.2
    (power_identity10 plusWeights0290) (power_identity10 minusWeights0290) g hg hmax

def envelope0290 : Envelope := ⟨coefficients0290, upper0290, bound0290⟩

def coefficients0291 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-125/32768), (-125/65536), (4625/524288)]

def upper0291 : ℚ := (1643/41943040000000)

def plusWeights0291 : Fin 11 → ℚ := ![(1643/41943040000000), (1643/4194304000000), (14787/8388608000000), (4929/1048576000000), (34503/4194304000000), (103509/10485760000000), (34503/4194304000000), (4929/1048576000000), (14467/8388608000000), (263/838860800000), 0]

def minusWeights0291 : Fin 11 → ℚ := ![(1643/41943040000000), (1643/4194304000000), (14787/8388608000000), (4929/1048576000000), (34503/4194304000000), (103509/10485760000000), (34503/4194304000000), (4929/1048576000000), (15107/8388608000000), (1971/4194304000000), (1643/20971520000000)]

theorem checked0291 :
    (∀ i, 0 ≤ plusWeights0291 i) ∧
    (∀ i, 0 ≤ minusWeights0291 i) ∧
    (∀ i, plusCoefficients coefficients0291 upper0291 i = powerCoefficients10 plusWeights0291 i) ∧
    (∀ i, minusCoefficients coefficients0291 upper0291 i = powerCoefficients10 minusWeights0291 i) := by
  decide +kernel

theorem bound0291 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0291 g| ≤ (upper0291 : ℝ) :=
  abs_of_coefficients coefficients0291 upper0291 powerCoefficients10 plusWeights0291 minusWeights0291
    checked0291.1 checked0291.2.1 checked0291.2.2.1 checked0291.2.2.2
    (power_identity10 plusWeights0291) (power_identity10 minusWeights0291) g hg hmax

def envelope0291 : Envelope := ⟨coefficients0291, upper0291, bound0291⟩

def coefficients0292 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-25/16384), (-25/32768), (-125/262144)]

def upper0292 : ℚ := (337/20971520000000)

def plusWeights0292 : Fin 11 → ℚ := ![(337/20971520000000), (337/2097152000000), (3033/4194304000000), (1011/524288000000), (7077/2097152000000), (21231/5242880000000), (7077/2097152000000), (1011/524288000000), (2969/4194304000000), (1357/10485760000000), 0]

def minusWeights0292 : Fin 11 → ℚ := ![(337/20971520000000), (337/2097152000000), (3033/4194304000000), (1011/524288000000), (7077/2097152000000), (21231/5242880000000), (7077/2097152000000), (1011/524288000000), (3097/4194304000000), (2013/10485760000000), (337/10485760000000)]

theorem checked0292 :
    (∀ i, 0 ≤ plusWeights0292 i) ∧
    (∀ i, 0 ≤ minusWeights0292 i) ∧
    (∀ i, plusCoefficients coefficients0292 upper0292 i = powerCoefficients10 plusWeights0292 i) ∧
    (∀ i, minusCoefficients coefficients0292 upper0292 i = powerCoefficients10 minusWeights0292 i) := by
  decide +kernel

theorem bound0292 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0292 g| ≤ (upper0292 : ℝ) :=
  abs_of_coefficients coefficients0292 upper0292 powerCoefficients10 plusWeights0292 minusWeights0292
    checked0292.1 checked0292.2.1 checked0292.2.2.1 checked0292.2.2.2
    (power_identity10 plusWeights0292) (power_identity10 minusWeights0292) g hg hmax

def envelope0292 : Envelope := ⟨coefficients0292, upper0292, bound0292⟩

def coefficients0293 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-525/8192), (-525/16384)]

def upper0293 : ℚ := (441/6553600000000)

def plusWeights0293 : Fin 11 → ℚ := ![(441/6553600000000), (441/655360000000), (3969/1310720000000), (1323/163840000000), (9261/655360000000), (27783/1638400000000), (9261/655360000000), (1323/163840000000), (3969/1310720000000), (399/655360000000), 0]

def minusWeights0293 : Fin 11 → ℚ := ![(441/6553600000000), (441/655360000000), (3969/1310720000000), (1323/163840000000), (9261/655360000000), (27783/1638400000000), (9261/655360000000), (1323/163840000000), (3969/1310720000000), (483/655360000000), (441/3276800000000)]

theorem checked0293 :
    (∀ i, 0 ≤ plusWeights0293 i) ∧
    (∀ i, 0 ≤ minusWeights0293 i) ∧
    (∀ i, plusCoefficients coefficients0293 upper0293 i = powerCoefficients10 plusWeights0293 i) ∧
    (∀ i, minusCoefficients coefficients0293 upper0293 i = powerCoefficients10 minusWeights0293 i) := by
  decide +kernel

theorem bound0293 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0293 g| ≤ (upper0293 : ℝ) :=
  abs_of_coefficients coefficients0293 upper0293 powerCoefficients10 plusWeights0293 minusWeights0293
    checked0293.1 checked0293.2.1 checked0293.2.2.1 checked0293.2.2.2
    (power_identity10 plusWeights0293) (power_identity10 minusWeights0293) g hg hmax

def envelope0293 : Envelope := ⟨coefficients0293, upper0293, bound0293⟩

def coefficients0294 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-975/16384), (-975/32768)]

def upper0294 : ℚ := (819/13107200000000)

def plusWeights0294 : Fin 11 → ℚ := ![(819/13107200000000), (819/1310720000000), (7371/2621440000000), (2457/327680000000), (17199/1310720000000), (51597/3276800000000), (17199/1310720000000), (2457/327680000000), (7371/2621440000000), (741/1310720000000), 0]

def minusWeights0294 : Fin 11 → ℚ := ![(819/13107200000000), (819/1310720000000), (7371/2621440000000), (2457/327680000000), (17199/1310720000000), (51597/3276800000000), (17199/1310720000000), (2457/327680000000), (7371/2621440000000), (897/1310720000000), (819/6553600000000)]

theorem checked0294 :
    (∀ i, 0 ≤ plusWeights0294 i) ∧
    (∀ i, 0 ≤ minusWeights0294 i) ∧
    (∀ i, plusCoefficients coefficients0294 upper0294 i = powerCoefficients10 plusWeights0294 i) ∧
    (∀ i, minusCoefficients coefficients0294 upper0294 i = powerCoefficients10 minusWeights0294 i) := by
  decide +kernel

theorem bound0294 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0294 g| ≤ (upper0294 : ℝ) :=
  abs_of_coefficients coefficients0294 upper0294 powerCoefficients10 plusWeights0294 minusWeights0294
    checked0294.1 checked0294.2.1 checked0294.2.2.1 checked0294.2.2.2
    (power_identity10 plusWeights0294) (power_identity10 minusWeights0294) g hg hmax

def envelope0294 : Envelope := ⟨coefficients0294, upper0294, bound0294⟩

def coefficients0295 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-225/4096), (-225/8192)]

def upper0295 : ℚ := (189/3276800000000)

def plusWeights0295 : Fin 11 → ℚ := ![(189/3276800000000), (189/327680000000), (1701/655360000000), (567/81920000000), (3969/327680000000), (11907/819200000000), (3969/327680000000), (567/81920000000), (1701/655360000000), (171/327680000000), 0]

def minusWeights0295 : Fin 11 → ℚ := ![(189/3276800000000), (189/327680000000), (1701/655360000000), (567/81920000000), (3969/327680000000), (11907/819200000000), (3969/327680000000), (567/81920000000), (1701/655360000000), (207/327680000000), (189/1638400000000)]

theorem checked0295 :
    (∀ i, 0 ≤ plusWeights0295 i) ∧
    (∀ i, 0 ≤ minusWeights0295 i) ∧
    (∀ i, plusCoefficients coefficients0295 upper0295 i = powerCoefficients10 plusWeights0295 i) ∧
    (∀ i, minusCoefficients coefficients0295 upper0295 i = powerCoefficients10 minusWeights0295 i) := by
  decide +kernel

theorem bound0295 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0295 g| ≤ (upper0295 : ℝ) :=
  abs_of_coefficients coefficients0295 upper0295 powerCoefficients10 plusWeights0295 minusWeights0295
    checked0295.1 checked0295.2.1 checked0295.2.2.1 checked0295.2.2.2
    (power_identity10 plusWeights0295) (power_identity10 minusWeights0295) g hg hmax

def envelope0295 : Envelope := ⟨coefficients0295, upper0295, bound0295⟩

def coefficients0296 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-825/16384), (-825/32768)]

def upper0296 : ℚ := (693/13107200000000)

def plusWeights0296 : Fin 11 → ℚ := ![(693/13107200000000), (693/1310720000000), (6237/2621440000000), (2079/327680000000), (14553/1310720000000), (43659/3276800000000), (14553/1310720000000), (2079/327680000000), (6237/2621440000000), (627/1310720000000), 0]

def minusWeights0296 : Fin 11 → ℚ := ![(693/13107200000000), (693/1310720000000), (6237/2621440000000), (2079/327680000000), (14553/1310720000000), (43659/3276800000000), (14553/1310720000000), (2079/327680000000), (6237/2621440000000), (759/1310720000000), (693/6553600000000)]

theorem checked0296 :
    (∀ i, 0 ≤ plusWeights0296 i) ∧
    (∀ i, 0 ≤ minusWeights0296 i) ∧
    (∀ i, plusCoefficients coefficients0296 upper0296 i = powerCoefficients10 plusWeights0296 i) ∧
    (∀ i, minusCoefficients coefficients0296 upper0296 i = powerCoefficients10 minusWeights0296 i) := by
  decide +kernel

theorem bound0296 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0296 g| ≤ (upper0296 : ℝ) :=
  abs_of_coefficients coefficients0296 upper0296 powerCoefficients10 plusWeights0296 minusWeights0296
    checked0296.1 checked0296.2.1 checked0296.2.2.1 checked0296.2.2.2
    (power_identity10 plusWeights0296) (power_identity10 minusWeights0296) g hg hmax

def envelope0296 : Envelope := ⟨coefficients0296, upper0296, bound0296⟩

def coefficients0297 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-375/8192), (-375/16384)]

def upper0297 : ℚ := (63/1310720000000)

def plusWeights0297 : Fin 11 → ℚ := ![(63/1310720000000), (63/131072000000), (567/262144000000), (189/32768000000), (1323/131072000000), (3969/327680000000), (1323/131072000000), (189/32768000000), (567/262144000000), (57/131072000000), 0]

def minusWeights0297 : Fin 11 → ℚ := ![(63/1310720000000), (63/131072000000), (567/262144000000), (189/32768000000), (1323/131072000000), (3969/327680000000), (1323/131072000000), (189/32768000000), (567/262144000000), (69/131072000000), (63/655360000000)]

theorem checked0297 :
    (∀ i, 0 ≤ plusWeights0297 i) ∧
    (∀ i, 0 ≤ minusWeights0297 i) ∧
    (∀ i, plusCoefficients coefficients0297 upper0297 i = powerCoefficients10 plusWeights0297 i) ∧
    (∀ i, minusCoefficients coefficients0297 upper0297 i = powerCoefficients10 minusWeights0297 i) := by
  decide +kernel

theorem bound0297 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0297 g| ≤ (upper0297 : ℝ) :=
  abs_of_coefficients coefficients0297 upper0297 powerCoefficients10 plusWeights0297 minusWeights0297
    checked0297.1 checked0297.2.1 checked0297.2.2.1 checked0297.2.2.2
    (power_identity10 plusWeights0297) (power_identity10 minusWeights0297) g hg hmax

def envelope0297 : Envelope := ⟨coefficients0297, upper0297, bound0297⟩

def coefficients0298 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-675/16384), (-675/32768)]

def upper0298 : ℚ := (567/13107200000000)

def plusWeights0298 : Fin 11 → ℚ := ![(567/13107200000000), (567/1310720000000), (5103/2621440000000), (1701/327680000000), (11907/1310720000000), (35721/3276800000000), (11907/1310720000000), (1701/327680000000), (5103/2621440000000), (513/1310720000000), 0]

def minusWeights0298 : Fin 11 → ℚ := ![(567/13107200000000), (567/1310720000000), (5103/2621440000000), (1701/327680000000), (11907/1310720000000), (35721/3276800000000), (11907/1310720000000), (1701/327680000000), (5103/2621440000000), (621/1310720000000), (567/6553600000000)]

theorem checked0298 :
    (∀ i, 0 ≤ plusWeights0298 i) ∧
    (∀ i, 0 ≤ minusWeights0298 i) ∧
    (∀ i, plusCoefficients coefficients0298 upper0298 i = powerCoefficients10 plusWeights0298 i) ∧
    (∀ i, minusCoefficients coefficients0298 upper0298 i = powerCoefficients10 minusWeights0298 i) := by
  decide +kernel

theorem bound0298 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0298 g| ≤ (upper0298 : ℝ) :=
  abs_of_coefficients coefficients0298 upper0298 powerCoefficients10 plusWeights0298 minusWeights0298
    checked0298.1 checked0298.2.1 checked0298.2.2.1 checked0298.2.2.2
    (power_identity10 plusWeights0298) (power_identity10 minusWeights0298) g hg hmax

def envelope0298 : Envelope := ⟨coefficients0298, upper0298, bound0298⟩

def coefficients0299 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-75/2048), (-75/4096)]

def upper0299 : ℚ := (63/1638400000000)

def plusWeights0299 : Fin 11 → ℚ := ![(63/1638400000000), (63/163840000000), (567/327680000000), (189/40960000000), (1323/163840000000), (3969/409600000000), (1323/163840000000), (189/40960000000), (567/327680000000), (57/163840000000), 0]

def minusWeights0299 : Fin 11 → ℚ := ![(63/1638400000000), (63/163840000000), (567/327680000000), (189/40960000000), (1323/163840000000), (3969/409600000000), (1323/163840000000), (189/40960000000), (567/327680000000), (69/163840000000), (63/819200000000)]

theorem checked0299 :
    (∀ i, 0 ≤ plusWeights0299 i) ∧
    (∀ i, 0 ≤ minusWeights0299 i) ∧
    (∀ i, plusCoefficients coefficients0299 upper0299 i = powerCoefficients10 plusWeights0299 i) ∧
    (∀ i, minusCoefficients coefficients0299 upper0299 i = powerCoefficients10 minusWeights0299 i) := by
  decide +kernel

theorem bound0299 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0299 g| ≤ (upper0299 : ℝ) :=
  abs_of_coefficients coefficients0299 upper0299 powerCoefficients10 plusWeights0299 minusWeights0299
    checked0299.1 checked0299.2.1 checked0299.2.2.1 checked0299.2.2.2
    (power_identity10 plusWeights0299) (power_identity10 minusWeights0299) g hg hmax

def envelope0299 : Envelope := ⟨coefficients0299, upper0299, bound0299⟩

def coefficients0300 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-225/8192), (-225/16384)]

def upper0300 : ℚ := (189/6553600000000)

def plusWeights0300 : Fin 11 → ℚ := ![(189/6553600000000), (189/655360000000), (1701/1310720000000), (567/163840000000), (3969/655360000000), (11907/1638400000000), (3969/655360000000), (567/163840000000), (1701/1310720000000), (171/655360000000), 0]

def minusWeights0300 : Fin 11 → ℚ := ![(189/6553600000000), (189/655360000000), (1701/1310720000000), (567/163840000000), (3969/655360000000), (11907/1638400000000), (3969/655360000000), (567/163840000000), (1701/1310720000000), (207/655360000000), (189/3276800000000)]

theorem checked0300 :
    (∀ i, 0 ≤ plusWeights0300 i) ∧
    (∀ i, 0 ≤ minusWeights0300 i) ∧
    (∀ i, plusCoefficients coefficients0300 upper0300 i = powerCoefficients10 plusWeights0300 i) ∧
    (∀ i, minusCoefficients coefficients0300 upper0300 i = powerCoefficients10 minusWeights0300 i) := by
  decide +kernel

theorem bound0300 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0300 g| ≤ (upper0300 : ℝ) :=
  abs_of_coefficients coefficients0300 upper0300 powerCoefficients10 plusWeights0300 minusWeights0300
    checked0300.1 checked0300.2.1 checked0300.2.2.1 checked0300.2.2.2
    (power_identity10 plusWeights0300) (power_identity10 minusWeights0300) g hg hmax

def envelope0300 : Envelope := ⟨coefficients0300, upper0300, bound0300⟩

def coefficients0301 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-825/32768), (-825/65536)]

def upper0301 : ℚ := (693/26214400000000)

def plusWeights0301 : Fin 11 → ℚ := ![(693/26214400000000), (693/2621440000000), (6237/5242880000000), (2079/655360000000), (14553/2621440000000), (43659/6553600000000), (14553/2621440000000), (2079/655360000000), (6237/5242880000000), (627/2621440000000), 0]

def minusWeights0301 : Fin 11 → ℚ := ![(693/26214400000000), (693/2621440000000), (6237/5242880000000), (2079/655360000000), (14553/2621440000000), (43659/6553600000000), (14553/2621440000000), (2079/655360000000), (6237/5242880000000), (759/2621440000000), (693/13107200000000)]

theorem checked0301 :
    (∀ i, 0 ≤ plusWeights0301 i) ∧
    (∀ i, 0 ≤ minusWeights0301 i) ∧
    (∀ i, plusCoefficients coefficients0301 upper0301 i = powerCoefficients10 plusWeights0301 i) ∧
    (∀ i, minusCoefficients coefficients0301 upper0301 i = powerCoefficients10 minusWeights0301 i) := by
  decide +kernel

theorem bound0301 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0301 g| ≤ (upper0301 : ℝ) :=
  abs_of_coefficients coefficients0301 upper0301 powerCoefficients10 plusWeights0301 minusWeights0301
    checked0301.1 checked0301.2.1 checked0301.2.2.1 checked0301.2.2.2
    (power_identity10 plusWeights0301) (power_identity10 minusWeights0301) g hg hmax

def envelope0301 : Envelope := ⟨coefficients0301, upper0301, bound0301⟩

def coefficients0302 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-375/16384), (-375/32768)]

def upper0302 : ℚ := (63/2621440000000)

def plusWeights0302 : Fin 11 → ℚ := ![(63/2621440000000), (63/262144000000), (567/524288000000), (189/65536000000), (1323/262144000000), (3969/655360000000), (1323/262144000000), (189/65536000000), (567/524288000000), (57/262144000000), 0]

def minusWeights0302 : Fin 11 → ℚ := ![(63/2621440000000), (63/262144000000), (567/524288000000), (189/65536000000), (1323/262144000000), (3969/655360000000), (1323/262144000000), (189/65536000000), (567/524288000000), (69/262144000000), (63/1310720000000)]

theorem checked0302 :
    (∀ i, 0 ≤ plusWeights0302 i) ∧
    (∀ i, 0 ≤ minusWeights0302 i) ∧
    (∀ i, plusCoefficients coefficients0302 upper0302 i = powerCoefficients10 plusWeights0302 i) ∧
    (∀ i, minusCoefficients coefficients0302 upper0302 i = powerCoefficients10 minusWeights0302 i) := by
  decide +kernel

theorem bound0302 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0302 g| ≤ (upper0302 : ℝ) :=
  abs_of_coefficients coefficients0302 upper0302 powerCoefficients10 plusWeights0302 minusWeights0302
    checked0302.1 checked0302.2.1 checked0302.2.2.1 checked0302.2.2.2
    (power_identity10 plusWeights0302) (power_identity10 minusWeights0302) g hg hmax

def envelope0302 : Envelope := ⟨coefficients0302, upper0302, bound0302⟩

def coefficients0303 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-675/32768), (-675/65536)]

def upper0303 : ℚ := (567/26214400000000)

def plusWeights0303 : Fin 11 → ℚ := ![(567/26214400000000), (567/2621440000000), (5103/5242880000000), (1701/655360000000), (11907/2621440000000), (35721/6553600000000), (11907/2621440000000), (1701/655360000000), (5103/5242880000000), (513/2621440000000), 0]

def minusWeights0303 : Fin 11 → ℚ := ![(567/26214400000000), (567/2621440000000), (5103/5242880000000), (1701/655360000000), (11907/2621440000000), (35721/6553600000000), (11907/2621440000000), (1701/655360000000), (5103/5242880000000), (621/2621440000000), (567/13107200000000)]

theorem checked0303 :
    (∀ i, 0 ≤ plusWeights0303 i) ∧
    (∀ i, 0 ≤ minusWeights0303 i) ∧
    (∀ i, plusCoefficients coefficients0303 upper0303 i = powerCoefficients10 plusWeights0303 i) ∧
    (∀ i, minusCoefficients coefficients0303 upper0303 i = powerCoefficients10 minusWeights0303 i) := by
  decide +kernel

theorem bound0303 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0303 g| ≤ (upper0303 : ℝ) :=
  abs_of_coefficients coefficients0303 upper0303 powerCoefficients10 plusWeights0303 minusWeights0303
    checked0303.1 checked0303.2.1 checked0303.2.2.1 checked0303.2.2.2
    (power_identity10 plusWeights0303) (power_identity10 minusWeights0303) g hg hmax

def envelope0303 : Envelope := ⟨coefficients0303, upper0303, bound0303⟩

def coefficients0304 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-75/4096), (-75/8192)]

def upper0304 : ℚ := (63/3276800000000)

def plusWeights0304 : Fin 11 → ℚ := ![(63/3276800000000), (63/327680000000), (567/655360000000), (189/81920000000), (1323/327680000000), (3969/819200000000), (1323/327680000000), (189/81920000000), (567/655360000000), (57/327680000000), 0]

def minusWeights0304 : Fin 11 → ℚ := ![(63/3276800000000), (63/327680000000), (567/655360000000), (189/81920000000), (1323/327680000000), (3969/819200000000), (1323/327680000000), (189/81920000000), (567/655360000000), (69/327680000000), (63/1638400000000)]

theorem checked0304 :
    (∀ i, 0 ≤ plusWeights0304 i) ∧
    (∀ i, 0 ≤ minusWeights0304 i) ∧
    (∀ i, plusCoefficients coefficients0304 upper0304 i = powerCoefficients10 plusWeights0304 i) ∧
    (∀ i, minusCoefficients coefficients0304 upper0304 i = powerCoefficients10 minusWeights0304 i) := by
  decide +kernel

theorem bound0304 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0304 g| ≤ (upper0304 : ℝ) :=
  abs_of_coefficients coefficients0304 upper0304 powerCoefficients10 plusWeights0304 minusWeights0304
    checked0304.1 checked0304.2.1 checked0304.2.2.1 checked0304.2.2.2
    (power_identity10 plusWeights0304) (power_identity10 minusWeights0304) g hg hmax

def envelope0304 : Envelope := ⟨coefficients0304, upper0304, bound0304⟩

def coefficients0305 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-525/32768), (-525/65536)]

def upper0305 : ℚ := (441/26214400000000)

def plusWeights0305 : Fin 11 → ℚ := ![(441/26214400000000), (441/2621440000000), (3969/5242880000000), (1323/655360000000), (9261/2621440000000), (27783/6553600000000), (9261/2621440000000), (1323/655360000000), (3969/5242880000000), (399/2621440000000), 0]

def minusWeights0305 : Fin 11 → ℚ := ![(441/26214400000000), (441/2621440000000), (3969/5242880000000), (1323/655360000000), (9261/2621440000000), (27783/6553600000000), (9261/2621440000000), (1323/655360000000), (3969/5242880000000), (483/2621440000000), (441/13107200000000)]

theorem checked0305 :
    (∀ i, 0 ≤ plusWeights0305 i) ∧
    (∀ i, 0 ≤ minusWeights0305 i) ∧
    (∀ i, plusCoefficients coefficients0305 upper0305 i = powerCoefficients10 plusWeights0305 i) ∧
    (∀ i, minusCoefficients coefficients0305 upper0305 i = powerCoefficients10 minusWeights0305 i) := by
  decide +kernel

theorem bound0305 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0305 g| ≤ (upper0305 : ℝ) :=
  abs_of_coefficients coefficients0305 upper0305 powerCoefficients10 plusWeights0305 minusWeights0305
    checked0305.1 checked0305.2.1 checked0305.2.2.1 checked0305.2.2.2
    (power_identity10 plusWeights0305) (power_identity10 minusWeights0305) g hg hmax

def envelope0305 : Envelope := ⟨coefficients0305, upper0305, bound0305⟩

def coefficients0306 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-475/32768), (-475/65536)]

def upper0306 : ℚ := (399/26214400000000)

def plusWeights0306 : Fin 11 → ℚ := ![(399/26214400000000), (399/2621440000000), (3591/5242880000000), (1197/655360000000), (8379/2621440000000), (25137/6553600000000), (8379/2621440000000), (1197/655360000000), (3591/5242880000000), (361/2621440000000), 0]

def minusWeights0306 : Fin 11 → ℚ := ![(399/26214400000000), (399/2621440000000), (3591/5242880000000), (1197/655360000000), (8379/2621440000000), (25137/6553600000000), (8379/2621440000000), (1197/655360000000), (3591/5242880000000), (437/2621440000000), (399/13107200000000)]

theorem checked0306 :
    (∀ i, 0 ≤ plusWeights0306 i) ∧
    (∀ i, 0 ≤ minusWeights0306 i) ∧
    (∀ i, plusCoefficients coefficients0306 upper0306 i = powerCoefficients10 plusWeights0306 i) ∧
    (∀ i, minusCoefficients coefficients0306 upper0306 i = powerCoefficients10 minusWeights0306 i) := by
  decide +kernel

theorem bound0306 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0306 g| ≤ (upper0306 : ℝ) :=
  abs_of_coefficients coefficients0306 upper0306 powerCoefficients10 plusWeights0306 minusWeights0306
    checked0306.1 checked0306.2.1 checked0306.2.2.1 checked0306.2.2.2
    (power_identity10 plusWeights0306) (power_identity10 minusWeights0306) g hg hmax

def envelope0306 : Envelope := ⟨coefficients0306, upper0306, bound0306⟩

def coefficients0307 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-225/16384), (-225/32768)]

def upper0307 : ℚ := (189/13107200000000)

def plusWeights0307 : Fin 11 → ℚ := ![(189/13107200000000), (189/1310720000000), (1701/2621440000000), (567/327680000000), (3969/1310720000000), (11907/3276800000000), (3969/1310720000000), (567/327680000000), (1701/2621440000000), (171/1310720000000), 0]

def minusWeights0307 : Fin 11 → ℚ := ![(189/13107200000000), (189/1310720000000), (1701/2621440000000), (567/327680000000), (3969/1310720000000), (11907/3276800000000), (3969/1310720000000), (567/327680000000), (1701/2621440000000), (207/1310720000000), (189/6553600000000)]

theorem checked0307 :
    (∀ i, 0 ≤ plusWeights0307 i) ∧
    (∀ i, 0 ≤ minusWeights0307 i) ∧
    (∀ i, plusCoefficients coefficients0307 upper0307 i = powerCoefficients10 plusWeights0307 i) ∧
    (∀ i, minusCoefficients coefficients0307 upper0307 i = powerCoefficients10 minusWeights0307 i) := by
  decide +kernel

theorem bound0307 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0307 g| ≤ (upper0307 : ℝ) :=
  abs_of_coefficients coefficients0307 upper0307 powerCoefficients10 plusWeights0307 minusWeights0307
    checked0307.1 checked0307.2.1 checked0307.2.2.1 checked0307.2.2.2
    (power_identity10 plusWeights0307) (power_identity10 minusWeights0307) g hg hmax

def envelope0307 : Envelope := ⟨coefficients0307, upper0307, bound0307⟩

def coefficients0308 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-375/32768), (-375/65536)]

def upper0308 : ℚ := (63/5242880000000)

def plusWeights0308 : Fin 11 → ℚ := ![(63/5242880000000), (63/524288000000), (567/1048576000000), (189/131072000000), (1323/524288000000), (3969/1310720000000), (1323/524288000000), (189/131072000000), (567/1048576000000), (57/524288000000), 0]

def minusWeights0308 : Fin 11 → ℚ := ![(63/5242880000000), (63/524288000000), (567/1048576000000), (189/131072000000), (1323/524288000000), (3969/1310720000000), (1323/524288000000), (189/131072000000), (567/1048576000000), (69/524288000000), (63/2621440000000)]

theorem checked0308 :
    (∀ i, 0 ≤ plusWeights0308 i) ∧
    (∀ i, 0 ≤ minusWeights0308 i) ∧
    (∀ i, plusCoefficients coefficients0308 upper0308 i = powerCoefficients10 plusWeights0308 i) ∧
    (∀ i, minusCoefficients coefficients0308 upper0308 i = powerCoefficients10 minusWeights0308 i) := by
  decide +kernel

theorem bound0308 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0308 g| ≤ (upper0308 : ℝ) :=
  abs_of_coefficients coefficients0308 upper0308 powerCoefficients10 plusWeights0308 minusWeights0308
    checked0308.1 checked0308.2.1 checked0308.2.2.1 checked0308.2.2.2
    (power_identity10 plusWeights0308) (power_identity10 minusWeights0308) g hg hmax

def envelope0308 : Envelope := ⟨coefficients0308, upper0308, bound0308⟩

def coefficients0309 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-325/32768), (-325/65536)]

def upper0309 : ℚ := (273/26214400000000)

def plusWeights0309 : Fin 11 → ℚ := ![(273/26214400000000), (273/2621440000000), (2457/5242880000000), (819/655360000000), (5733/2621440000000), (17199/6553600000000), (5733/2621440000000), (819/655360000000), (2457/5242880000000), (247/2621440000000), 0]

def minusWeights0309 : Fin 11 → ℚ := ![(273/26214400000000), (273/2621440000000), (2457/5242880000000), (819/655360000000), (5733/2621440000000), (17199/6553600000000), (5733/2621440000000), (819/655360000000), (2457/5242880000000), (299/2621440000000), (273/13107200000000)]

theorem checked0309 :
    (∀ i, 0 ≤ plusWeights0309 i) ∧
    (∀ i, 0 ≤ minusWeights0309 i) ∧
    (∀ i, plusCoefficients coefficients0309 upper0309 i = powerCoefficients10 plusWeights0309 i) ∧
    (∀ i, minusCoefficients coefficients0309 upper0309 i = powerCoefficients10 minusWeights0309 i) := by
  decide +kernel

theorem bound0309 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0309 g| ≤ (upper0309 : ℝ) :=
  abs_of_coefficients coefficients0309 upper0309 powerCoefficients10 plusWeights0309 minusWeights0309
    checked0309.1 checked0309.2.1 checked0309.2.2.1 checked0309.2.2.2
    (power_identity10 plusWeights0309) (power_identity10 minusWeights0309) g hg hmax

def envelope0309 : Envelope := ⟨coefficients0309, upper0309, bound0309⟩

def coefficients0310 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-75/8192), (-75/16384)]

def upper0310 : ℚ := (63/6553600000000)

def plusWeights0310 : Fin 11 → ℚ := ![(63/6553600000000), (63/655360000000), (567/1310720000000), (189/163840000000), (1323/655360000000), (3969/1638400000000), (1323/655360000000), (189/163840000000), (567/1310720000000), (57/655360000000), 0]

def minusWeights0310 : Fin 11 → ℚ := ![(63/6553600000000), (63/655360000000), (567/1310720000000), (189/163840000000), (1323/655360000000), (3969/1638400000000), (1323/655360000000), (189/163840000000), (567/1310720000000), (69/655360000000), (63/3276800000000)]

theorem checked0310 :
    (∀ i, 0 ≤ plusWeights0310 i) ∧
    (∀ i, 0 ≤ minusWeights0310 i) ∧
    (∀ i, plusCoefficients coefficients0310 upper0310 i = powerCoefficients10 plusWeights0310 i) ∧
    (∀ i, minusCoefficients coefficients0310 upper0310 i = powerCoefficients10 minusWeights0310 i) := by
  decide +kernel

theorem bound0310 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0310 g| ≤ (upper0310 : ℝ) :=
  abs_of_coefficients coefficients0310 upper0310 powerCoefficients10 plusWeights0310 minusWeights0310
    checked0310.1 checked0310.2.1 checked0310.2.2.1 checked0310.2.2.2
    (power_identity10 plusWeights0310) (power_identity10 minusWeights0310) g hg hmax

def envelope0310 : Envelope := ⟨coefficients0310, upper0310, bound0310⟩

def coefficients0311 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-125/16384), (-125/32768)]

def upper0311 : ℚ := (21/2621440000000)

def plusWeights0311 : Fin 11 → ℚ := ![(21/2621440000000), (21/262144000000), (189/524288000000), (63/65536000000), (441/262144000000), (1323/655360000000), (441/262144000000), (63/65536000000), (189/524288000000), (19/262144000000), 0]

def minusWeights0311 : Fin 11 → ℚ := ![(21/2621440000000), (21/262144000000), (189/524288000000), (63/65536000000), (441/262144000000), (1323/655360000000), (441/262144000000), (63/65536000000), (189/524288000000), (23/262144000000), (21/1310720000000)]

theorem checked0311 :
    (∀ i, 0 ≤ plusWeights0311 i) ∧
    (∀ i, 0 ≤ minusWeights0311 i) ∧
    (∀ i, plusCoefficients coefficients0311 upper0311 i = powerCoefficients10 plusWeights0311 i) ∧
    (∀ i, minusCoefficients coefficients0311 upper0311 i = powerCoefficients10 minusWeights0311 i) := by
  decide +kernel

theorem bound0311 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0311 g| ≤ (upper0311 : ℝ) :=
  abs_of_coefficients coefficients0311 upper0311 powerCoefficients10 plusWeights0311 minusWeights0311
    checked0311.1 checked0311.2.1 checked0311.2.2.1 checked0311.2.2.2
    (power_identity10 plusWeights0311) (power_identity10 minusWeights0311) g hg hmax

def envelope0311 : Envelope := ⟨coefficients0311, upper0311, bound0311⟩

def coefficients0312 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-225/32768), (-225/65536)]

def upper0312 : ℚ := (189/26214400000000)

def plusWeights0312 : Fin 11 → ℚ := ![(189/26214400000000), (189/2621440000000), (1701/5242880000000), (567/655360000000), (3969/2621440000000), (11907/6553600000000), (3969/2621440000000), (567/655360000000), (1701/5242880000000), (171/2621440000000), 0]

def minusWeights0312 : Fin 11 → ℚ := ![(189/26214400000000), (189/2621440000000), (1701/5242880000000), (567/655360000000), (3969/2621440000000), (11907/6553600000000), (3969/2621440000000), (567/655360000000), (1701/5242880000000), (207/2621440000000), (189/13107200000000)]

theorem checked0312 :
    (∀ i, 0 ≤ plusWeights0312 i) ∧
    (∀ i, 0 ≤ minusWeights0312 i) ∧
    (∀ i, plusCoefficients coefficients0312 upper0312 i = powerCoefficients10 plusWeights0312 i) ∧
    (∀ i, minusCoefficients coefficients0312 upper0312 i = powerCoefficients10 minusWeights0312 i) := by
  decide +kernel

theorem bound0312 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0312 g| ≤ (upper0312 : ℝ) :=
  abs_of_coefficients coefficients0312 upper0312 powerCoefficients10 plusWeights0312 minusWeights0312
    checked0312.1 checked0312.2.1 checked0312.2.2.1 checked0312.2.2.2
    (power_identity10 plusWeights0312) (power_identity10 minusWeights0312) g hg hmax

def envelope0312 : Envelope := ⟨coefficients0312, upper0312, bound0312⟩

def coefficients0313 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-75/16384), (-75/32768)]

def upper0313 : ℚ := (63/13107200000000)

def plusWeights0313 : Fin 11 → ℚ := ![(63/13107200000000), (63/1310720000000), (567/2621440000000), (189/327680000000), (1323/1310720000000), (3969/3276800000000), (1323/1310720000000), (189/327680000000), (567/2621440000000), (57/1310720000000), 0]

def minusWeights0313 : Fin 11 → ℚ := ![(63/13107200000000), (63/1310720000000), (567/2621440000000), (189/327680000000), (1323/1310720000000), (3969/3276800000000), (1323/1310720000000), (189/327680000000), (567/2621440000000), (69/1310720000000), (63/6553600000000)]

theorem checked0313 :
    (∀ i, 0 ≤ plusWeights0313 i) ∧
    (∀ i, 0 ≤ minusWeights0313 i) ∧
    (∀ i, plusCoefficients coefficients0313 upper0313 i = powerCoefficients10 plusWeights0313 i) ∧
    (∀ i, minusCoefficients coefficients0313 upper0313 i = powerCoefficients10 minusWeights0313 i) := by
  decide +kernel

theorem bound0313 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0313 g| ≤ (upper0313 : ℝ) :=
  abs_of_coefficients coefficients0313 upper0313 powerCoefficients10 plusWeights0313 minusWeights0313
    checked0313.1 checked0313.2.1 checked0313.2.2.1 checked0313.2.2.2
    (power_identity10 plusWeights0313) (power_identity10 minusWeights0313) g hg hmax

def envelope0313 : Envelope := ⟨coefficients0313, upper0313, bound0313⟩

def coefficients0314 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-25/8192), (-25/16384)]

def upper0314 : ℚ := (21/6553600000000)

def plusWeights0314 : Fin 11 → ℚ := ![(21/6553600000000), (21/655360000000), (189/1310720000000), (63/163840000000), (441/655360000000), (1323/1638400000000), (441/655360000000), (63/163840000000), (189/1310720000000), (19/655360000000), 0]

def minusWeights0314 : Fin 11 → ℚ := ![(21/6553600000000), (21/655360000000), (189/1310720000000), (63/163840000000), (441/655360000000), (1323/1638400000000), (441/655360000000), (63/163840000000), (189/1310720000000), (23/655360000000), (21/3276800000000)]

theorem checked0314 :
    (∀ i, 0 ≤ plusWeights0314 i) ∧
    (∀ i, 0 ≤ minusWeights0314 i) ∧
    (∀ i, plusCoefficients coefficients0314 upper0314 i = powerCoefficients10 plusWeights0314 i) ∧
    (∀ i, minusCoefficients coefficients0314 upper0314 i = powerCoefficients10 minusWeights0314 i) := by
  decide +kernel

theorem bound0314 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0314 g| ≤ (upper0314 : ℝ) :=
  abs_of_coefficients coefficients0314 upper0314 powerCoefficients10 plusWeights0314 minusWeights0314
    checked0314.1 checked0314.2.1 checked0314.2.2.1 checked0314.2.2.2
    (power_identity10 plusWeights0314) (power_identity10 minusWeights0314) g hg hmax

def envelope0314 : Envelope := ⟨coefficients0314, upper0314, bound0314⟩

def coefficients0315 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-25/16384), (-25/32768)]

def upper0315 : ℚ := (21/13107200000000)

def plusWeights0315 : Fin 11 → ℚ := ![(21/13107200000000), (21/1310720000000), (189/2621440000000), (63/327680000000), (441/1310720000000), (1323/3276800000000), (441/1310720000000), (63/327680000000), (189/2621440000000), (19/1310720000000), 0]

def minusWeights0315 : Fin 11 → ℚ := ![(21/13107200000000), (21/1310720000000), (189/2621440000000), (63/327680000000), (441/1310720000000), (1323/3276800000000), (441/1310720000000), (63/327680000000), (189/2621440000000), (23/1310720000000), (21/6553600000000)]

theorem checked0315 :
    (∀ i, 0 ≤ plusWeights0315 i) ∧
    (∀ i, 0 ≤ minusWeights0315 i) ∧
    (∀ i, plusCoefficients coefficients0315 upper0315 i = powerCoefficients10 plusWeights0315 i) ∧
    (∀ i, minusCoefficients coefficients0315 upper0315 i = powerCoefficients10 minusWeights0315 i) := by
  decide +kernel

theorem bound0315 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0315 g| ≤ (upper0315 : ℝ) :=
  abs_of_coefficients coefficients0315 upper0315 powerCoefficients10 plusWeights0315 minusWeights0315
    checked0315.1 checked0315.2.1 checked0315.2.2.1 checked0315.2.2.2
    (power_identity10 plusWeights0315) (power_identity10 minusWeights0315) g hg hmax

def envelope0315 : Envelope := ⟨coefficients0315, upper0315, bound0315⟩

def coefficients0316 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (375/131072)]

def upper0316 : ℚ := (3/10485760000000)

def plusWeights0316 : Fin 11 → ℚ := ![(3/10485760000000), (3/1048576000000), (27/2097152000000), (9/262144000000), (63/1048576000000), (189/2621440000000), (63/1048576000000), (9/262144000000), (27/2097152000000), (3/1048576000000), (3/5242880000000)]

def minusWeights0316 : Fin 11 → ℚ := ![(3/10485760000000), (3/1048576000000), (27/2097152000000), (9/262144000000), (63/1048576000000), (189/2621440000000), (63/1048576000000), (9/262144000000), (27/2097152000000), (3/1048576000000), 0]

theorem checked0316 :
    (∀ i, 0 ≤ plusWeights0316 i) ∧
    (∀ i, 0 ≤ minusWeights0316 i) ∧
    (∀ i, plusCoefficients coefficients0316 upper0316 i = powerCoefficients10 plusWeights0316 i) ∧
    (∀ i, minusCoefficients coefficients0316 upper0316 i = powerCoefficients10 minusWeights0316 i) := by
  decide +kernel

theorem bound0316 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0316 g| ≤ (upper0316 : ℝ) :=
  abs_of_coefficients coefficients0316 upper0316 powerCoefficients10 plusWeights0316 minusWeights0316
    checked0316.1 checked0316.2.1 checked0316.2.2.1 checked0316.2.2.2
    (power_identity10 plusWeights0316) (power_identity10 minusWeights0316) g hg hmax

def envelope0316 : Envelope := ⟨coefficients0316, upper0316, bound0316⟩

def coefficients0317 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (375/65536)]

def upper0317 : ℚ := (3/5242880000000)

def plusWeights0317 : Fin 11 → ℚ := ![(3/5242880000000), (3/524288000000), (27/1048576000000), (9/131072000000), (63/524288000000), (189/1310720000000), (63/524288000000), (9/131072000000), (27/1048576000000), (3/524288000000), (3/2621440000000)]

def minusWeights0317 : Fin 11 → ℚ := ![(3/5242880000000), (3/524288000000), (27/1048576000000), (9/131072000000), (63/524288000000), (189/1310720000000), (63/524288000000), (9/131072000000), (27/1048576000000), (3/524288000000), 0]

theorem checked0317 :
    (∀ i, 0 ≤ plusWeights0317 i) ∧
    (∀ i, 0 ≤ minusWeights0317 i) ∧
    (∀ i, plusCoefficients coefficients0317 upper0317 i = powerCoefficients10 plusWeights0317 i) ∧
    (∀ i, minusCoefficients coefficients0317 upper0317 i = powerCoefficients10 minusWeights0317 i) := by
  decide +kernel

theorem bound0317 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0317 g| ≤ (upper0317 : ℝ) :=
  abs_of_coefficients coefficients0317 upper0317 powerCoefficients10 plusWeights0317 minusWeights0317
    checked0317.1 checked0317.2.1 checked0317.2.2.1 checked0317.2.2.2
    (power_identity10 plusWeights0317) (power_identity10 minusWeights0317) g hg hmax

def envelope0317 : Envelope := ⟨coefficients0317, upper0317, bound0317⟩

def coefficients0318 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1125/131072)]

def upper0318 : ℚ := (9/10485760000000)

def plusWeights0318 : Fin 11 → ℚ := ![(9/10485760000000), (9/1048576000000), (81/2097152000000), (27/262144000000), (189/1048576000000), (567/2621440000000), (189/1048576000000), (27/262144000000), (81/2097152000000), (9/1048576000000), (9/5242880000000)]

def minusWeights0318 : Fin 11 → ℚ := ![(9/10485760000000), (9/1048576000000), (81/2097152000000), (27/262144000000), (189/1048576000000), (567/2621440000000), (189/1048576000000), (27/262144000000), (81/2097152000000), (9/1048576000000), 0]

theorem checked0318 :
    (∀ i, 0 ≤ plusWeights0318 i) ∧
    (∀ i, 0 ≤ minusWeights0318 i) ∧
    (∀ i, plusCoefficients coefficients0318 upper0318 i = powerCoefficients10 plusWeights0318 i) ∧
    (∀ i, minusCoefficients coefficients0318 upper0318 i = powerCoefficients10 minusWeights0318 i) := by
  decide +kernel

theorem bound0318 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0318 g| ≤ (upper0318 : ℝ) :=
  abs_of_coefficients coefficients0318 upper0318 powerCoefficients10 plusWeights0318 minusWeights0318
    checked0318.1 checked0318.2.1 checked0318.2.2.1 checked0318.2.2.2
    (power_identity10 plusWeights0318) (power_identity10 minusWeights0318) g hg hmax

def envelope0318 : Envelope := ⟨coefficients0318, upper0318, bound0318⟩

def coefficients0319 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1875/131072)]

def upper0319 : ℚ := (3/2097152000000)

def plusWeights0319 : Fin 11 → ℚ := ![(3/2097152000000), (3/209715200000), (27/419430400000), (9/52428800000), (63/209715200000), (189/524288000000), (63/209715200000), (9/52428800000), (27/419430400000), (3/209715200000), (3/1048576000000)]

def minusWeights0319 : Fin 11 → ℚ := ![(3/2097152000000), (3/209715200000), (27/419430400000), (9/52428800000), (63/209715200000), (189/524288000000), (63/209715200000), (9/52428800000), (27/419430400000), (3/209715200000), 0]

theorem checked0319 :
    (∀ i, 0 ≤ plusWeights0319 i) ∧
    (∀ i, 0 ≤ minusWeights0319 i) ∧
    (∀ i, plusCoefficients coefficients0319 upper0319 i = powerCoefficients10 plusWeights0319 i) ∧
    (∀ i, minusCoefficients coefficients0319 upper0319 i = powerCoefficients10 minusWeights0319 i) := by
  decide +kernel

theorem bound0319 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0319 g| ≤ (upper0319 : ℝ) :=
  abs_of_coefficients coefficients0319 upper0319 powerCoefficients10 plusWeights0319 minusWeights0319
    checked0319.1 checked0319.2.1 checked0319.2.2.1 checked0319.2.2.2
    (power_identity10 plusWeights0319) (power_identity10 minusWeights0319) g hg hmax

def envelope0319 : Envelope := ⟨coefficients0319, upper0319, bound0319⟩

end BilayerDressed.CubicQuarticEnvelopes

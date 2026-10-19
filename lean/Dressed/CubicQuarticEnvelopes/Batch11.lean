import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0352 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (15/1024), (15/1024), (15/4096)]

def upper0352 : ℚ := (1323/8192000000000)

def plusWeights0352 : Fin 11 → ℚ := ![(1323/8192000000000), (1323/819200000000), (11907/1638400000000), (3969/204800000000), (27783/819200000000), (83349/2048000000000), (27783/819200000000), (3969/204800000000), (12147/1638400000000), (63/32768000000), (1323/4096000000000)]

def minusWeights0352 : Fin 11 → ℚ := ![(1323/8192000000000), (1323/819200000000), (11907/1638400000000), (3969/204800000000), (27783/819200000000), (83349/2048000000000), (27783/819200000000), (3969/204800000000), (11667/1638400000000), (1071/819200000000), 0]

theorem checked0352 :
    (∀ i, 0 ≤ plusWeights0352 i) ∧
    (∀ i, 0 ≤ minusWeights0352 i) ∧
    (∀ i, plusCoefficients coefficients0352 upper0352 i = powerCoefficients10 plusWeights0352 i) ∧
    (∀ i, minusCoefficients coefficients0352 upper0352 i = powerCoefficients10 minusWeights0352 i) := by
  decide +kernel

theorem bound0352 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0352 g| ≤ (upper0352 : ℝ) :=
  abs_of_coefficients coefficients0352 upper0352 powerCoefficients10 plusWeights0352 minusWeights0352
    checked0352.1 checked0352.2.1 checked0352.2.2.1 checked0352.2.2.2
    (power_identity10 plusWeights0352) (power_identity10 minusWeights0352) g hg hmax

def envelope0352 : Envelope := ⟨coefficients0352, upper0352, bound0352⟩

def coefficients0353 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/8192), (195/16384), (1245/65536)]

def upper0353 : ℚ := (23409/131072000000000)

def plusWeights0353 : Fin 11 → ℚ := ![(23409/131072000000000), (23409/13107200000000), (210681/26214400000000), (70227/3276800000000), (491589/13107200000000), (1474767/32768000000000), (491589/13107200000000), (70227/3276800000000), (215001/26214400000000), (5577/2621440000000), (23409/65536000000000)]

def minusWeights0353 : Fin 11 → ℚ := ![(23409/131072000000000), (23409/13107200000000), (210681/26214400000000), (70227/3276800000000), (491589/13107200000000), (1474767/32768000000000), (491589/13107200000000), (70227/3276800000000), (206361/26214400000000), (18933/13107200000000), 0]

theorem checked0353 :
    (∀ i, 0 ≤ plusWeights0353 i) ∧
    (∀ i, 0 ≤ minusWeights0353 i) ∧
    (∀ i, plusCoefficients coefficients0353 upper0353 i = powerCoefficients10 plusWeights0353 i) ∧
    (∀ i, minusCoefficients coefficients0353 upper0353 i = powerCoefficients10 minusWeights0353 i) := by
  decide +kernel

theorem bound0353 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0353 g| ≤ (upper0353 : ℝ) :=
  abs_of_coefficients coefficients0353 upper0353 powerCoefficients10 plusWeights0353 minusWeights0353
    checked0353.1 checked0353.2.1 checked0353.2.2.1 checked0353.2.2.2
    (power_identity10 plusWeights0353) (power_identity10 minusWeights0353) g hg hmax

def envelope0353 : Envelope := ⟨coefficients0353, upper0353, bound0353⟩

def coefficients0354 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/8192), (195/16384), (405/16384)]

def upper0354 : ℚ := (5871/32768000000000)

def plusWeights0354 : Fin 11 → ℚ := ![(5871/32768000000000), (5871/3276800000000), (52839/6553600000000), (17613/819200000000), (123291/3276800000000), (369873/8192000000000), (123291/3276800000000), (17613/819200000000), (53919/6553600000000), (699/327680000000), (5871/16384000000000)]

def minusWeights0354 : Fin 11 → ℚ := ![(5871/32768000000000), (5871/3276800000000), (52839/6553600000000), (17613/819200000000), (123291/3276800000000), (369873/8192000000000), (123291/3276800000000), (17613/819200000000), (51759/6553600000000), (297/204800000000), 0]

theorem checked0354 :
    (∀ i, 0 ≤ plusWeights0354 i) ∧
    (∀ i, 0 ≤ minusWeights0354 i) ∧
    (∀ i, plusCoefficients coefficients0354 upper0354 i = powerCoefficients10 plusWeights0354 i) ∧
    (∀ i, minusCoefficients coefficients0354 upper0354 i = powerCoefficients10 minusWeights0354 i) := by
  decide +kernel

theorem bound0354 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0354 g| ≤ (upper0354 : ℝ) :=
  abs_of_coefficients coefficients0354 upper0354 powerCoefficients10 plusWeights0354 minusWeights0354
    checked0354.1 checked0354.2.1 checked0354.2.2.1 checked0354.2.2.2
    (power_identity10 plusWeights0354) (power_identity10 minusWeights0354) g hg hmax

def envelope0354 : Envelope := ⟨coefficients0354, upper0354, bound0354⟩

def coefficients0355 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/8192), (195/16384), (1155/16384)]

def upper0355 : ℚ := (6021/32768000000000)

def plusWeights0355 : Fin 11 → ℚ := ![(6021/32768000000000), (6021/3276800000000), (54189/6553600000000), (18063/819200000000), (126441/3276800000000), (379323/8192000000000), (126441/3276800000000), (18063/819200000000), (55269/6553600000000), (357/163840000000), (6021/16384000000000)]

def minusWeights0355 : Fin 11 → ℚ := ![(6021/32768000000000), (6021/3276800000000), (54189/6553600000000), (18063/819200000000), (126441/3276800000000), (379323/8192000000000), (126441/3276800000000), (18063/819200000000), (53109/6553600000000), (2451/1638400000000), 0]

theorem checked0355 :
    (∀ i, 0 ≤ plusWeights0355 i) ∧
    (∀ i, 0 ≤ minusWeights0355 i) ∧
    (∀ i, plusCoefficients coefficients0355 upper0355 i = powerCoefficients10 plusWeights0355 i) ∧
    (∀ i, minusCoefficients coefficients0355 upper0355 i = powerCoefficients10 minusWeights0355 i) := by
  decide +kernel

theorem bound0355 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0355 g| ≤ (upper0355 : ℝ) :=
  abs_of_coefficients coefficients0355 upper0355 powerCoefficients10 plusWeights0355 minusWeights0355
    checked0355.1 checked0355.2.1 checked0355.2.2.1 checked0355.2.2.2
    (power_identity10 plusWeights0355) (power_identity10 minusWeights0355) g hg hmax

def envelope0355 : Envelope := ⟨coefficients0355, upper0355, bound0355⟩

def coefficients0356 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (555/32768), (735/65536), (2805/131072)]

def upper0356 : ℚ := (47901/262144000000000)

def plusWeights0356 : Fin 11 → ℚ := ![(47901/262144000000000), (47901/26214400000000), (431109/52428800000000), (143703/6553600000000), (1005921/26214400000000), (3017763/65536000000000), (1005921/26214400000000), (143703/6553600000000), (439989/52428800000000), (2283/1048576000000), (47901/131072000000000)]

def minusWeights0356 : Fin 11 → ℚ := ![(47901/262144000000000), (47901/26214400000000), (431109/52428800000000), (143703/6553600000000), (1005921/26214400000000), (3017763/65536000000000), (1005921/26214400000000), (143703/6553600000000), (422229/52428800000000), (38727/26214400000000), 0]

theorem checked0356 :
    (∀ i, 0 ≤ plusWeights0356 i) ∧
    (∀ i, 0 ≤ minusWeights0356 i) ∧
    (∀ i, plusCoefficients coefficients0356 upper0356 i = powerCoefficients10 plusWeights0356 i) ∧
    (∀ i, minusCoefficients coefficients0356 upper0356 i = powerCoefficients10 minusWeights0356 i) := by
  decide +kernel

theorem bound0356 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0356 g| ≤ (upper0356 : ℝ) :=
  abs_of_coefficients coefficients0356 upper0356 powerCoefficients10 plusWeights0356 minusWeights0356
    checked0356.1 checked0356.2.1 checked0356.2.2.1 checked0356.2.2.2
    (power_identity10 plusWeights0356) (power_identity10 minusWeights0356) g hg hmax

def envelope0356 : Envelope := ⟨coefficients0356, upper0356, bound0356⟩

def coefficients0357 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (285/16384), (345/32768), (405/32768)]

def upper0357 : ℚ := (12171/65536000000000)

def plusWeights0357 : Fin 11 → ℚ := ![(12171/65536000000000), (12171/6553600000000), (109539/13107200000000), (36513/1638400000000), (255591/6553600000000), (766773/16384000000000), (255591/6553600000000), (36513/1638400000000), (111819/13107200000000), (363/163840000000), (12171/32768000000000)]

def minusWeights0357 : Fin 11 → ℚ := ![(12171/65536000000000), (12171/6553600000000), (109539/13107200000000), (36513/1638400000000), (255591/6553600000000), (766773/16384000000000), (255591/6553600000000), (36513/1638400000000), (107259/13107200000000), (4911/3276800000000), 0]

theorem checked0357 :
    (∀ i, 0 ≤ plusWeights0357 i) ∧
    (∀ i, 0 ≤ minusWeights0357 i) ∧
    (∀ i, plusCoefficients coefficients0357 upper0357 i = powerCoefficients10 plusWeights0357 i) ∧
    (∀ i, minusCoefficients coefficients0357 upper0357 i = powerCoefficients10 minusWeights0357 i) := by
  decide +kernel

theorem bound0357 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0357 g| ≤ (upper0357 : ℝ) :=
  abs_of_coefficients coefficients0357 upper0357 powerCoefficients10 plusWeights0357 minusWeights0357
    checked0357.1 checked0357.2.1 checked0357.2.2.1 checked0357.2.2.2
    (power_identity10 plusWeights0357) (power_identity10 minusWeights0357) g hg hmax

def envelope0357 : Envelope := ⟨coefficients0357, upper0357, bound0357⟩

def coefficients0358 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/4096), (75/8192), (375/65536)]

def upper0358 : ℚ := (1011/5242880000000)

def plusWeights0358 : Fin 11 → ℚ := ![(1011/5242880000000), (1011/524288000000), (9099/1048576000000), (3033/131072000000), (21231/524288000000), (63693/1310720000000), (21231/524288000000), (3033/131072000000), (9291/1048576000000), (6039/2621440000000), (1011/2621440000000)]

def minusWeights0358 : Fin 11 → ℚ := ![(1011/5242880000000), (1011/524288000000), (9099/1048576000000), (3033/131072000000), (21231/524288000000), (63693/1310720000000), (21231/524288000000), (3033/131072000000), (8907/1048576000000), (4071/2621440000000), 0]

theorem checked0358 :
    (∀ i, 0 ≤ plusWeights0358 i) ∧
    (∀ i, 0 ≤ minusWeights0358 i) ∧
    (∀ i, plusCoefficients coefficients0358 upper0358 i = powerCoefficients10 plusWeights0358 i) ∧
    (∀ i, minusCoefficients coefficients0358 upper0358 i = powerCoefficients10 minusWeights0358 i) := by
  decide +kernel

theorem bound0358 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0358 g| ≤ (upper0358 : ℝ) :=
  abs_of_coefficients coefficients0358 upper0358 powerCoefficients10 plusWeights0358 minusWeights0358
    checked0358.1 checked0358.2.1 checked0358.2.2.1 checked0358.2.2.2
    (power_identity10 plusWeights0358) (power_identity10 minusWeights0358) g hg hmax

def envelope0358 : Envelope := ⟨coefficients0358, upper0358, bound0358⟩

def coefficients0359 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/4096), (75/8192), (375/32768)]

def upper0359 : ℚ := (507/2621440000000)

def plusWeights0359 : Fin 11 → ℚ := ![(507/2621440000000), (507/262144000000), (4563/524288000000), (1521/65536000000), (10647/262144000000), (31941/655360000000), (10647/262144000000), (1521/65536000000), (4659/524288000000), (3027/1310720000000), (507/1310720000000)]

def minusWeights0359 : Fin 11 → ℚ := ![(507/2621440000000), (507/262144000000), (4563/524288000000), (1521/65536000000), (10647/262144000000), (31941/655360000000), (10647/262144000000), (1521/65536000000), (4467/524288000000), (2043/1310720000000), 0]

theorem checked0359 :
    (∀ i, 0 ≤ plusWeights0359 i) ∧
    (∀ i, 0 ≤ minusWeights0359 i) ∧
    (∀ i, plusCoefficients coefficients0359 upper0359 i = powerCoefficients10 plusWeights0359 i) ∧
    (∀ i, minusCoefficients coefficients0359 upper0359 i = powerCoefficients10 minusWeights0359 i) := by
  decide +kernel

theorem bound0359 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0359 g| ≤ (upper0359 : ℝ) :=
  abs_of_coefficients coefficients0359 upper0359 powerCoefficients10 plusWeights0359 minusWeights0359
    checked0359.1 checked0359.2.1 checked0359.2.2.1 checked0359.2.2.2
    (power_identity10 plusWeights0359) (power_identity10 minusWeights0359) g hg hmax

def envelope0359 : Envelope := ⟨coefficients0359, upper0359, bound0359⟩

def coefficients0360 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/4096), (75/8192), (1875/32768)]

def upper0360 : ℚ := (519/2621440000000)

def plusWeights0360 : Fin 11 → ℚ := ![(519/2621440000000), (519/262144000000), (4671/524288000000), (1557/65536000000), (10899/262144000000), (32697/655360000000), (10899/262144000000), (1557/65536000000), (4767/524288000000), (3087/1310720000000), (519/1310720000000)]

def minusWeights0360 : Fin 11 → ℚ := ![(519/2621440000000), (519/262144000000), (4671/524288000000), (1557/65536000000), (10899/262144000000), (32697/655360000000), (10899/262144000000), (1557/65536000000), (183/20971520000), (2103/1310720000000), 0]

theorem checked0360 :
    (∀ i, 0 ≤ plusWeights0360 i) ∧
    (∀ i, 0 ≤ minusWeights0360 i) ∧
    (∀ i, plusCoefficients coefficients0360 upper0360 i = powerCoefficients10 plusWeights0360 i) ∧
    (∀ i, minusCoefficients coefficients0360 upper0360 i = powerCoefficients10 minusWeights0360 i) := by
  decide +kernel

theorem bound0360 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0360 g| ≤ (upper0360 : ℝ) :=
  abs_of_coefficients coefficients0360 upper0360 powerCoefficients10 plusWeights0360 minusWeights0360
    checked0360.1 checked0360.2.1 checked0360.2.2.1 checked0360.2.2.2
    (power_identity10 plusWeights0360) (power_identity10 minusWeights0360) g hg hmax

def envelope0360 : Envelope := ⟨coefficients0360, upper0360, bound0360⟩

def coefficients0361 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (5/256), (5/256), (5/1024)]

def upper0361 : ℚ := (441/2048000000000)

def plusWeights0361 : Fin 11 → ℚ := ![(441/2048000000000), (441/204800000000), (3969/409600000000), (1323/51200000000), (9261/204800000000), (27783/512000000000), (9261/204800000000), (1323/51200000000), (4049/409600000000), (21/8192000000), (441/1024000000000)]

def minusWeights0361 : Fin 11 → ℚ := ![(441/2048000000000), (441/204800000000), (3969/409600000000), (1323/51200000000), (9261/204800000000), (27783/512000000000), (9261/204800000000), (1323/51200000000), (3889/409600000000), (357/204800000000), 0]

theorem checked0361 :
    (∀ i, 0 ≤ plusWeights0361 i) ∧
    (∀ i, 0 ≤ minusWeights0361 i) ∧
    (∀ i, plusCoefficients coefficients0361 upper0361 i = powerCoefficients10 plusWeights0361 i) ∧
    (∀ i, minusCoefficients coefficients0361 upper0361 i = powerCoefficients10 minusWeights0361 i) := by
  decide +kernel

theorem bound0361 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0361 g| ≤ (upper0361 : ℝ) :=
  abs_of_coefficients coefficients0361 upper0361 powerCoefficients10 plusWeights0361 minusWeights0361
    checked0361.1 checked0361.2.1 checked0361.2.2.1 checked0361.2.2.2
    (power_identity10 plusWeights0361) (power_identity10 minusWeights0361) g hg hmax

def envelope0361 : Envelope := ⟨coefficients0361, upper0361, bound0361⟩

def coefficients0362 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (675/32768), (675/65536), (3375/262144)]

def upper0362 : ℚ := (4563/20971520000000)

def plusWeights0362 : Fin 11 → ℚ := ![(4563/20971520000000), (4563/2097152000000), (41067/4194304000000), (13689/524288000000), (95823/2097152000000), (287469/5242880000000), (95823/2097152000000), (13689/524288000000), (41931/4194304000000), (27243/10485760000000), (4563/10485760000000)]

def minusWeights0362 : Fin 11 → ℚ := ![(4563/20971520000000), (4563/2097152000000), (41067/4194304000000), (13689/524288000000), (95823/2097152000000), (287469/5242880000000), (95823/2097152000000), (13689/524288000000), (40203/4194304000000), (18387/10485760000000), 0]

theorem checked0362 :
    (∀ i, 0 ≤ plusWeights0362 i) ∧
    (∀ i, 0 ≤ minusWeights0362 i) ∧
    (∀ i, plusCoefficients coefficients0362 upper0362 i = powerCoefficients10 plusWeights0362 i) ∧
    (∀ i, minusCoefficients coefficients0362 upper0362 i = powerCoefficients10 minusWeights0362 i) := by
  decide +kernel

theorem bound0362 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0362 g| ≤ (upper0362 : ℝ) :=
  abs_of_coefficients coefficients0362 upper0362 powerCoefficients10 plusWeights0362 minusWeights0362
    checked0362.1 checked0362.2.1 checked0362.2.2.1 checked0362.2.2.2
    (power_identity10 plusWeights0362) (power_identity10 minusWeights0362) g hg hmax

def envelope0362 : Envelope := ⟨coefficients0362, upper0362, bound0362⟩

def coefficients0363 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (45/2048), (45/2048), (45/8192)]

def upper0363 : ℚ := (3969/16384000000000)

def plusWeights0363 : Fin 11 → ℚ := ![(3969/16384000000000), (3969/1638400000000), (35721/3276800000000), (11907/409600000000), (83349/1638400000000), (250047/4096000000000), (83349/1638400000000), (11907/409600000000), (36441/3276800000000), (189/65536000000), (3969/8192000000000)]

def minusWeights0363 : Fin 11 → ℚ := ![(3969/16384000000000), (3969/1638400000000), (35721/3276800000000), (11907/409600000000), (83349/1638400000000), (250047/4096000000000), (83349/1638400000000), (11907/409600000000), (35001/3276800000000), (3213/1638400000000), 0]

theorem checked0363 :
    (∀ i, 0 ≤ plusWeights0363 i) ∧
    (∀ i, 0 ≤ minusWeights0363 i) ∧
    (∀ i, plusCoefficients coefficients0363 upper0363 i = powerCoefficients10 plusWeights0363 i) ∧
    (∀ i, minusCoefficients coefficients0363 upper0363 i = powerCoefficients10 minusWeights0363 i) := by
  decide +kernel

theorem bound0363 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0363 g| ≤ (upper0363 : ℝ) :=
  abs_of_coefficients coefficients0363 upper0363 powerCoefficients10 plusWeights0363 minusWeights0363
    checked0363.1 checked0363.2.1 checked0363.2.2.1 checked0363.2.2.2
    (power_identity10 plusWeights0363) (power_identity10 minusWeights0363) g hg hmax

def envelope0363 : Envelope := ⟨coefficients0363, upper0363, bound0363⟩

def coefficients0364 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (25/1024), (25/1024), (25/4096)]

def upper0364 : ℚ := (441/1638400000000)

def plusWeights0364 : Fin 11 → ℚ := ![(441/1638400000000), (441/163840000000), (3969/327680000000), (1323/40960000000), (9261/163840000000), (27783/409600000000), (9261/163840000000), (1323/40960000000), (4049/327680000000), (21/6553600000), (441/819200000000)]

def minusWeights0364 : Fin 11 → ℚ := ![(441/1638400000000), (441/163840000000), (3969/327680000000), (1323/40960000000), (9261/163840000000), (27783/409600000000), (9261/163840000000), (1323/40960000000), (3889/327680000000), (357/163840000000), 0]

theorem checked0364 :
    (∀ i, 0 ≤ plusWeights0364 i) ∧
    (∀ i, 0 ≤ minusWeights0364 i) ∧
    (∀ i, plusCoefficients coefficients0364 upper0364 i = powerCoefficients10 plusWeights0364 i) ∧
    (∀ i, minusCoefficients coefficients0364 upper0364 i = powerCoefficients10 minusWeights0364 i) := by
  decide +kernel

theorem bound0364 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0364 g| ≤ (upper0364 : ℝ) :=
  abs_of_coefficients coefficients0364 upper0364 powerCoefficients10 plusWeights0364 minusWeights0364
    checked0364.1 checked0364.2.1 checked0364.2.2.1 checked0364.2.2.2
    (power_identity10 plusWeights0364) (power_identity10 minusWeights0364) g hg hmax

def envelope0364 : Envelope := ⟨coefficients0364, upper0364, bound0364⟩

def coefficients0365 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/16384), (585/32768), (3735/131072)]

def upper0365 : ℚ := (70227/262144000000000)

def plusWeights0365 : Fin 11 → ℚ := ![(70227/262144000000000), (70227/26214400000000), (632043/52428800000000), (210681/6553600000000), (1474767/26214400000000), (4424301/65536000000000), (1474767/26214400000000), (210681/6553600000000), (645003/52428800000000), (16731/5242880000000), (70227/131072000000000)]

def minusWeights0365 : Fin 11 → ℚ := ![(70227/262144000000000), (70227/26214400000000), (632043/52428800000000), (210681/6553600000000), (1474767/26214400000000), (4424301/65536000000000), (1474767/26214400000000), (210681/6553600000000), (619083/52428800000000), (56799/26214400000000), 0]

theorem checked0365 :
    (∀ i, 0 ≤ plusWeights0365 i) ∧
    (∀ i, 0 ≤ minusWeights0365 i) ∧
    (∀ i, plusCoefficients coefficients0365 upper0365 i = powerCoefficients10 plusWeights0365 i) ∧
    (∀ i, minusCoefficients coefficients0365 upper0365 i = powerCoefficients10 minusWeights0365 i) := by
  decide +kernel

theorem bound0365 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0365 g| ≤ (upper0365 : ℝ) :=
  abs_of_coefficients coefficients0365 upper0365 powerCoefficients10 plusWeights0365 minusWeights0365
    checked0365.1 checked0365.2.1 checked0365.2.2.1 checked0365.2.2.2
    (power_identity10 plusWeights0365) (power_identity10 minusWeights0365) g hg hmax

def envelope0365 : Envelope := ⟨coefficients0365, upper0365, bound0365⟩

def coefficients0366 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/16384), (585/32768), (1215/32768)]

def upper0366 : ℚ := (17613/65536000000000)

def plusWeights0366 : Fin 11 → ℚ := ![(17613/65536000000000), (17613/6553600000000), (158517/13107200000000), (52839/1638400000000), (369873/6553600000000), (1109619/16384000000000), (369873/6553600000000), (52839/1638400000000), (161757/13107200000000), (2097/655360000000), (17613/32768000000000)]

def minusWeights0366 : Fin 11 → ℚ := ![(17613/65536000000000), (17613/6553600000000), (158517/13107200000000), (52839/1638400000000), (369873/6553600000000), (1109619/16384000000000), (369873/6553600000000), (52839/1638400000000), (155277/13107200000000), (891/409600000000), 0]

theorem checked0366 :
    (∀ i, 0 ≤ plusWeights0366 i) ∧
    (∀ i, 0 ≤ minusWeights0366 i) ∧
    (∀ i, plusCoefficients coefficients0366 upper0366 i = powerCoefficients10 plusWeights0366 i) ∧
    (∀ i, minusCoefficients coefficients0366 upper0366 i = powerCoefficients10 minusWeights0366 i) := by
  decide +kernel

theorem bound0366 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0366 g| ≤ (upper0366 : ℝ) :=
  abs_of_coefficients coefficients0366 upper0366 powerCoefficients10 plusWeights0366 minusWeights0366
    checked0366.1 checked0366.2.1 checked0366.2.2.1 checked0366.2.2.2
    (power_identity10 plusWeights0366) (power_identity10 minusWeights0366) g hg hmax

def envelope0366 : Envelope := ⟨coefficients0366, upper0366, bound0366⟩

def coefficients0367 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/16384), (585/32768), (585/8192)]

def upper0367 : ℚ := (8919/32768000000000)

def plusWeights0367 : Fin 11 → ℚ := ![(8919/32768000000000), (8919/3276800000000), (80271/6553600000000), (26757/819200000000), (187299/3276800000000), (561897/8192000000000), (187299/3276800000000), (26757/819200000000), (81891/6553600000000), (4239/1310720000000), (8919/16384000000000)]

def minusWeights0367 : Fin 11 → ℚ := ![(8919/32768000000000), (8919/3276800000000), (80271/6553600000000), (26757/819200000000), (187299/3276800000000), (561897/8192000000000), (187299/3276800000000), (26757/819200000000), (78651/6553600000000), (14481/6553600000000), 0]

theorem checked0367 :
    (∀ i, 0 ≤ plusWeights0367 i) ∧
    (∀ i, 0 ≤ minusWeights0367 i) ∧
    (∀ i, plusCoefficients coefficients0367 upper0367 i = powerCoefficients10 plusWeights0367 i) ∧
    (∀ i, minusCoefficients coefficients0367 upper0367 i = powerCoefficients10 minusWeights0367 i) := by
  decide +kernel

theorem bound0367 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0367 g| ≤ (upper0367 : ℝ) :=
  abs_of_coefficients coefficients0367 upper0367 powerCoefficients10 plusWeights0367 minusWeights0367
    checked0367.1 checked0367.2.1 checked0367.2.2.1 checked0367.2.2.2
    (power_identity10 plusWeights0367) (power_identity10 minusWeights0367) g hg hmax

def envelope0367 : Envelope := ⟨coefficients0367, upper0367, bound0367⟩

def coefficients0368 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (225/8192), (225/16384), (1125/131072)]

def upper0368 : ℚ := (3033/10485760000000)

def plusWeights0368 : Fin 11 → ℚ := ![(3033/10485760000000), (3033/1048576000000), (27297/2097152000000), (9099/262144000000), (63693/1048576000000), (191079/2621440000000), (63693/1048576000000), (9099/262144000000), (27873/2097152000000), (18117/5242880000000), (3033/5242880000000)]

def minusWeights0368 : Fin 11 → ℚ := ![(3033/10485760000000), (3033/1048576000000), (27297/2097152000000), (9099/262144000000), (63693/1048576000000), (191079/2621440000000), (63693/1048576000000), (9099/262144000000), (26721/2097152000000), (12213/5242880000000), 0]

theorem checked0368 :
    (∀ i, 0 ≤ plusWeights0368 i) ∧
    (∀ i, 0 ≤ minusWeights0368 i) ∧
    (∀ i, plusCoefficients coefficients0368 upper0368 i = powerCoefficients10 plusWeights0368 i) ∧
    (∀ i, minusCoefficients coefficients0368 upper0368 i = powerCoefficients10 minusWeights0368 i) := by
  decide +kernel

theorem bound0368 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0368 g| ≤ (upper0368 : ℝ) :=
  abs_of_coefficients coefficients0368 upper0368 powerCoefficients10 plusWeights0368 minusWeights0368
    checked0368.1 checked0368.2.1 checked0368.2.2.1 checked0368.2.2.2
    (power_identity10 plusWeights0368) (power_identity10 minusWeights0368) g hg hmax

def envelope0368 : Envelope := ⟨coefficients0368, upper0368, bound0368⟩

def coefficients0369 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (15/512), (15/512), (15/2048)]

def upper0369 : ℚ := (1323/4096000000000)

def plusWeights0369 : Fin 11 → ℚ := ![(1323/4096000000000), (1323/409600000000), (11907/819200000000), (3969/102400000000), (27783/409600000000), (83349/1024000000000), (27783/409600000000), (3969/102400000000), (12147/819200000000), (63/16384000000), (1323/2048000000000)]

def minusWeights0369 : Fin 11 → ℚ := ![(1323/4096000000000), (1323/409600000000), (11907/819200000000), (3969/102400000000), (27783/409600000000), (83349/1024000000000), (27783/409600000000), (3969/102400000000), (11667/819200000000), (1071/409600000000), 0]

theorem checked0369 :
    (∀ i, 0 ≤ plusWeights0369 i) ∧
    (∀ i, 0 ≤ minusWeights0369 i) ∧
    (∀ i, plusCoefficients coefficients0369 upper0369 i = powerCoefficients10 plusWeights0369 i) ∧
    (∀ i, minusCoefficients coefficients0369 upper0369 i = powerCoefficients10 minusWeights0369 i) := by
  decide +kernel

theorem bound0369 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0369 g| ≤ (upper0369 : ℝ) :=
  abs_of_coefficients coefficients0369 upper0369 powerCoefficients10 plusWeights0369 minusWeights0369
    checked0369.1 checked0369.2.1 checked0369.2.2.1 checked0369.2.2.2
    (power_identity10 plusWeights0369) (power_identity10 minusWeights0369) g hg hmax

def envelope0369 : Envelope := ⟨coefficients0369, upper0369, bound0369⟩

def coefficients0370 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/4096), (195/8192), (5355/131072)]

def upper0370 : ℚ := (93711/262144000000000)

def plusWeights0370 : Fin 11 → ℚ := ![(93711/262144000000000), (93711/26214400000000), (843399/52428800000000), (281133/6553600000000), (1967931/26214400000000), (5903793/65536000000000), (1967931/26214400000000), (281133/6553600000000), (860679/52428800000000), (22323/5242880000000), (93711/131072000000000)]

def minusWeights0370 : Fin 11 → ℚ := ![(93711/262144000000000), (93711/26214400000000), (843399/52428800000000), (281133/6553600000000), (1967931/26214400000000), (5903793/65536000000000), (1967931/26214400000000), (281133/6553600000000), (826119/52428800000000), (75807/26214400000000), 0]

theorem checked0370 :
    (∀ i, 0 ≤ plusWeights0370 i) ∧
    (∀ i, 0 ≤ minusWeights0370 i) ∧
    (∀ i, plusCoefficients coefficients0370 upper0370 i = powerCoefficients10 plusWeights0370 i) ∧
    (∀ i, minusCoefficients coefficients0370 upper0370 i = powerCoefficients10 minusWeights0370 i) := by
  decide +kernel

theorem bound0370 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0370 g| ≤ (upper0370 : ℝ) :=
  abs_of_coefficients coefficients0370 upper0370 powerCoefficients10 plusWeights0370 minusWeights0370
    checked0370.1 checked0370.2.1 checked0370.2.2.1 checked0370.2.2.2
    (power_identity10 plusWeights0370) (power_identity10 minusWeights0370) g hg hmax

def envelope0370 : Envelope := ⟨coefficients0370, upper0370, bound0370⟩

def coefficients0371 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (555/16384), (735/32768), (2805/65536)]

def upper0371 : ℚ := (47901/131072000000000)

def plusWeights0371 : Fin 11 → ℚ := ![(47901/131072000000000), (47901/13107200000000), (431109/26214400000000), (143703/3276800000000), (1005921/13107200000000), (3017763/32768000000000), (1005921/13107200000000), (143703/3276800000000), (439989/26214400000000), (2283/524288000000), (47901/65536000000000)]

def minusWeights0371 : Fin 11 → ℚ := ![(47901/131072000000000), (47901/13107200000000), (431109/26214400000000), (143703/3276800000000), (1005921/13107200000000), (3017763/32768000000000), (1005921/13107200000000), (143703/3276800000000), (422229/26214400000000), (38727/13107200000000), 0]

theorem checked0371 :
    (∀ i, 0 ≤ plusWeights0371 i) ∧
    (∀ i, 0 ≤ minusWeights0371 i) ∧
    (∀ i, plusCoefficients coefficients0371 upper0371 i = powerCoefficients10 plusWeights0371 i) ∧
    (∀ i, minusCoefficients coefficients0371 upper0371 i = powerCoefficients10 minusWeights0371 i) := by
  decide +kernel

theorem bound0371 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0371 g| ≤ (upper0371 : ℝ) :=
  abs_of_coefficients coefficients0371 upper0371 powerCoefficients10 plusWeights0371 minusWeights0371
    checked0371.1 checked0371.2.1 checked0371.2.2.1 checked0371.2.2.2
    (power_identity10 plusWeights0371) (power_identity10 minusWeights0371) g hg hmax

def envelope0371 : Envelope := ⟨coefficients0371, upper0371, bound0371⟩

def coefficients0372 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/2048), (75/4096), (1875/131072)]

def upper0372 : ℚ := (4047/10485760000000)

def plusWeights0372 : Fin 11 → ℚ := ![(4047/10485760000000), (4047/1048576000000), (36423/2097152000000), (12141/262144000000), (84987/1048576000000), (254961/2621440000000), (84987/1048576000000), (12141/262144000000), (37191/2097152000000), (24171/5242880000000), (4047/5242880000000)]

def minusWeights0372 : Fin 11 → ℚ := ![(4047/10485760000000), (4047/1048576000000), (36423/2097152000000), (12141/262144000000), (84987/1048576000000), (254961/2621440000000), (84987/1048576000000), (12141/262144000000), (7131/419430400000), (16299/5242880000000), 0]

theorem checked0372 :
    (∀ i, 0 ≤ plusWeights0372 i) ∧
    (∀ i, 0 ≤ minusWeights0372 i) ∧
    (∀ i, plusCoefficients coefficients0372 upper0372 i = powerCoefficients10 plusWeights0372 i) ∧
    (∀ i, minusCoefficients coefficients0372 upper0372 i = powerCoefficients10 minusWeights0372 i) := by
  decide +kernel

theorem bound0372 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0372 g| ≤ (upper0372 : ℝ) :=
  abs_of_coefficients coefficients0372 upper0372 powerCoefficients10 plusWeights0372 minusWeights0372
    checked0372.1 checked0372.2.1 checked0372.2.2.1 checked0372.2.2.2
    (power_identity10 plusWeights0372) (power_identity10 minusWeights0372) g hg hmax

def envelope0372 : Envelope := ⟨coefficients0372, upper0372, bound0372⟩

def coefficients0373 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/2048), (75/2048), (75/8192)]

def upper0373 : ℚ := (1323/3276800000000)

def plusWeights0373 : Fin 11 → ℚ := ![(1323/3276800000000), (1323/327680000000), (11907/655360000000), (3969/81920000000), (27783/327680000000), (83349/819200000000), (27783/327680000000), (3969/81920000000), (12147/655360000000), (63/13107200000), (1323/1638400000000)]

def minusWeights0373 : Fin 11 → ℚ := ![(1323/3276800000000), (1323/327680000000), (11907/655360000000), (3969/81920000000), (27783/327680000000), (83349/819200000000), (27783/327680000000), (3969/81920000000), (11667/655360000000), (1071/327680000000), 0]

theorem checked0373 :
    (∀ i, 0 ≤ plusWeights0373 i) ∧
    (∀ i, 0 ≤ minusWeights0373 i) ∧
    (∀ i, plusCoefficients coefficients0373 upper0373 i = powerCoefficients10 plusWeights0373 i) ∧
    (∀ i, minusCoefficients coefficients0373 upper0373 i = powerCoefficients10 minusWeights0373 i) := by
  decide +kernel

theorem bound0373 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0373 g| ≤ (upper0373 : ℝ) :=
  abs_of_coefficients coefficients0373 upper0373 powerCoefficients10 plusWeights0373 minusWeights0373
    checked0373.1 checked0373.2.1 checked0373.2.2.1 checked0373.2.2.2
    (power_identity10 plusWeights0373) (power_identity10 minusWeights0373) g hg hmax

def envelope0373 : Envelope := ⟨coefficients0373, upper0373, bound0373⟩

def coefficients0374 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (5/128), (5/128), (5/512)]

def upper0374 : ℚ := (441/1024000000000)

def plusWeights0374 : Fin 11 → ℚ := ![(441/1024000000000), (441/102400000000), (3969/204800000000), (1323/25600000000), (9261/102400000000), (27783/256000000000), (9261/102400000000), (1323/25600000000), (4049/204800000000), (21/4096000000), (441/512000000000)]

def minusWeights0374 : Fin 11 → ℚ := ![(441/1024000000000), (441/102400000000), (3969/204800000000), (1323/25600000000), (9261/102400000000), (27783/256000000000), (9261/102400000000), (1323/25600000000), (3889/204800000000), (357/102400000000), 0]

theorem checked0374 :
    (∀ i, 0 ≤ plusWeights0374 i) ∧
    (∀ i, 0 ≤ minusWeights0374 i) ∧
    (∀ i, plusCoefficients coefficients0374 upper0374 i = powerCoefficients10 plusWeights0374 i) ∧
    (∀ i, minusCoefficients coefficients0374 upper0374 i = powerCoefficients10 minusWeights0374 i) := by
  decide +kernel

theorem bound0374 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0374 g| ≤ (upper0374 : ℝ) :=
  abs_of_coefficients coefficients0374 upper0374 powerCoefficients10 plusWeights0374 minusWeights0374
    checked0374.1 checked0374.2.1 checked0374.2.2.1 checked0374.2.2.2
    (power_identity10 plusWeights0374) (power_identity10 minusWeights0374) g hg hmax

def envelope0374 : Envelope := ⟨coefficients0374, upper0374, bound0374⟩

def coefficients0375 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (675/16384), (675/32768), (3375/131072)]

def upper0375 : ℚ := (4563/10485760000000)

def plusWeights0375 : Fin 11 → ℚ := ![(4563/10485760000000), (4563/1048576000000), (41067/2097152000000), (13689/262144000000), (95823/1048576000000), (287469/2621440000000), (95823/1048576000000), (13689/262144000000), (41931/2097152000000), (27243/5242880000000), (4563/5242880000000)]

def minusWeights0375 : Fin 11 → ℚ := ![(4563/10485760000000), (4563/1048576000000), (41067/2097152000000), (13689/262144000000), (95823/1048576000000), (287469/2621440000000), (95823/1048576000000), (13689/262144000000), (40203/2097152000000), (18387/5242880000000), 0]

theorem checked0375 :
    (∀ i, 0 ≤ plusWeights0375 i) ∧
    (∀ i, 0 ≤ minusWeights0375 i) ∧
    (∀ i, plusCoefficients coefficients0375 upper0375 i = powerCoefficients10 plusWeights0375 i) ∧
    (∀ i, minusCoefficients coefficients0375 upper0375 i = powerCoefficients10 minusWeights0375 i) := by
  decide +kernel

theorem bound0375 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0375 g| ≤ (upper0375 : ℝ) :=
  abs_of_coefficients coefficients0375 upper0375 powerCoefficients10 plusWeights0375 minusWeights0375
    checked0375.1 checked0375.2.1 checked0375.2.2.1 checked0375.2.2.2
    (power_identity10 plusWeights0375) (power_identity10 minusWeights0375) g hg hmax

def envelope0375 : Envelope := ⟨coefficients0375, upper0375, bound0375⟩

def coefficients0376 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (675/16384), (975/32768), (6225/131072)]

def upper0376 : ℚ := (23409/52428800000000)

def plusWeights0376 : Fin 11 → ℚ := ![(23409/52428800000000), (23409/5242880000000), (210681/10485760000000), (70227/1310720000000), (491589/5242880000000), (1474767/13107200000000), (491589/5242880000000), (70227/1310720000000), (215001/10485760000000), (5577/1048576000000), (23409/26214400000000)]

def minusWeights0376 : Fin 11 → ℚ := ![(23409/52428800000000), (23409/5242880000000), (210681/10485760000000), (70227/1310720000000), (491589/5242880000000), (1474767/13107200000000), (491589/5242880000000), (70227/1310720000000), (206361/10485760000000), (18933/5242880000000), 0]

theorem checked0376 :
    (∀ i, 0 ≤ plusWeights0376 i) ∧
    (∀ i, 0 ≤ minusWeights0376 i) ∧
    (∀ i, plusCoefficients coefficients0376 upper0376 i = powerCoefficients10 plusWeights0376 i) ∧
    (∀ i, minusCoefficients coefficients0376 upper0376 i = powerCoefficients10 minusWeights0376 i) := by
  decide +kernel

theorem bound0376 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0376 g| ≤ (upper0376 : ℝ) :=
  abs_of_coefficients coefficients0376 upper0376 powerCoefficients10 plusWeights0376 minusWeights0376
    checked0376.1 checked0376.2.1 checked0376.2.2.1 checked0376.2.2.2
    (power_identity10 plusWeights0376) (power_identity10 minusWeights0376) g hg hmax

def envelope0376 : Envelope := ⟨coefficients0376, upper0376, bound0376⟩

def coefficients0377 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (45/1024), (45/1024), (45/4096)]

def upper0377 : ℚ := (3969/8192000000000)

def plusWeights0377 : Fin 11 → ℚ := ![(3969/8192000000000), (3969/819200000000), (35721/1638400000000), (11907/204800000000), (83349/819200000000), (250047/2048000000000), (83349/819200000000), (11907/204800000000), (36441/1638400000000), (189/32768000000), (3969/4096000000000)]

def minusWeights0377 : Fin 11 → ℚ := ![(3969/8192000000000), (3969/819200000000), (35721/1638400000000), (11907/204800000000), (83349/819200000000), (250047/2048000000000), (83349/819200000000), (11907/204800000000), (35001/1638400000000), (3213/819200000000), 0]

theorem checked0377 :
    (∀ i, 0 ≤ plusWeights0377 i) ∧
    (∀ i, 0 ≤ minusWeights0377 i) ∧
    (∀ i, plusCoefficients coefficients0377 upper0377 i = powerCoefficients10 plusWeights0377 i) ∧
    (∀ i, minusCoefficients coefficients0377 upper0377 i = powerCoefficients10 minusWeights0377 i) := by
  decide +kernel

theorem bound0377 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0377 g| ≤ (upper0377 : ℝ) :=
  abs_of_coefficients coefficients0377 upper0377 powerCoefficients10 plusWeights0377 minusWeights0377
    checked0377.1 checked0377.2.1 checked0377.2.2.1 checked0377.2.2.2
    (power_identity10 plusWeights0377) (power_identity10 minusWeights0377) g hg hmax

def envelope0377 : Envelope := ⟨coefficients0377, upper0377, bound0377⟩

def coefficients0378 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/8192), (585/16384), (1215/16384)]

def upper0378 : ℚ := (17613/32768000000000)

def plusWeights0378 : Fin 11 → ℚ := ![(17613/32768000000000), (17613/3276800000000), (158517/6553600000000), (52839/819200000000), (369873/3276800000000), (1109619/8192000000000), (369873/3276800000000), (52839/819200000000), (161757/6553600000000), (2097/327680000000), (17613/16384000000000)]

def minusWeights0378 : Fin 11 → ℚ := ![(17613/32768000000000), (17613/3276800000000), (158517/6553600000000), (52839/819200000000), (369873/3276800000000), (1109619/8192000000000), (369873/3276800000000), (52839/819200000000), (155277/6553600000000), (891/204800000000), 0]

theorem checked0378 :
    (∀ i, 0 ≤ plusWeights0378 i) ∧
    (∀ i, 0 ≤ minusWeights0378 i) ∧
    (∀ i, plusCoefficients coefficients0378 upper0378 i = powerCoefficients10 plusWeights0378 i) ∧
    (∀ i, minusCoefficients coefficients0378 upper0378 i = powerCoefficients10 minusWeights0378 i) := by
  decide +kernel

theorem bound0378 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0378 g| ≤ (upper0378 : ℝ) :=
  abs_of_coefficients coefficients0378 upper0378 powerCoefficients10 plusWeights0378 minusWeights0378
    checked0378.1 checked0378.2.1 checked0378.2.2.1 checked0378.2.2.2
    (power_identity10 plusWeights0378) (power_identity10 minusWeights0378) g hg hmax

def envelope0378 : Envelope := ⟨coefficients0378, upper0378, bound0378⟩

def coefficients0379 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/8192), (585/16384), (10845/131072)]

def upper0379 : ℚ := (141129/262144000000000)

def plusWeights0379 : Fin 11 → ℚ := ![(141129/262144000000000), (141129/26214400000000), (1270161/52428800000000), (423387/6553600000000), (2963709/26214400000000), (8891127/65536000000000), (2963709/26214400000000), (423387/6553600000000), (1296081/52428800000000), (33597/5242880000000), (141129/131072000000000)]

def minusWeights0379 : Fin 11 → ℚ := ![(141129/262144000000000), (141129/26214400000000), (1270161/52428800000000), (423387/6553600000000), (2963709/26214400000000), (8891127/65536000000000), (2963709/26214400000000), (423387/6553600000000), (1244241/52428800000000), (114273/26214400000000), 0]

theorem checked0379 :
    (∀ i, 0 ≤ plusWeights0379 i) ∧
    (∀ i, 0 ≤ minusWeights0379 i) ∧
    (∀ i, plusCoefficients coefficients0379 upper0379 i = powerCoefficients10 plusWeights0379 i) ∧
    (∀ i, minusCoefficients coefficients0379 upper0379 i = powerCoefficients10 minusWeights0379 i) := by
  decide +kernel

theorem bound0379 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0379 g| ≤ (upper0379 : ℝ) :=
  abs_of_coefficients coefficients0379 upper0379 powerCoefficients10 plusWeights0379 minusWeights0379
    checked0379.1 checked0379.2.1 checked0379.2.2.1 checked0379.2.2.2
    (power_identity10 plusWeights0379) (power_identity10 minusWeights0379) g hg hmax

def envelope0379 : Envelope := ⟨coefficients0379, upper0379, bound0379⟩

def coefficients0380 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (15/256), (15/256), (15/1024)]

def upper0380 : ℚ := (1323/2048000000000)

def plusWeights0380 : Fin 11 → ℚ := ![(1323/2048000000000), (1323/204800000000), (11907/409600000000), (3969/51200000000), (27783/204800000000), (83349/512000000000), (27783/204800000000), (3969/51200000000), (12147/409600000000), (63/8192000000), (1323/1024000000000)]

def minusWeights0380 : Fin 11 → ℚ := ![(1323/2048000000000), (1323/204800000000), (11907/409600000000), (3969/51200000000), (27783/204800000000), (83349/512000000000), (27783/204800000000), (3969/51200000000), (11667/409600000000), (1071/204800000000), 0]

theorem checked0380 :
    (∀ i, 0 ≤ plusWeights0380 i) ∧
    (∀ i, 0 ≤ minusWeights0380 i) ∧
    (∀ i, plusCoefficients coefficients0380 upper0380 i = powerCoefficients10 plusWeights0380 i) ∧
    (∀ i, minusCoefficients coefficients0380 upper0380 i = powerCoefficients10 minusWeights0380 i) := by
  decide +kernel

theorem bound0380 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0380 g| ≤ (upper0380 : ℝ) :=
  abs_of_coefficients coefficients0380 upper0380 powerCoefficients10 plusWeights0380 minusWeights0380
    checked0380.1 checked0380.2.1 checked0380.2.2.1 checked0380.2.2.2
    (power_identity10 plusWeights0380) (power_identity10 minusWeights0380) g hg hmax

def envelope0380 : Envelope := ⟨coefficients0380, upper0380, bound0380⟩

def coefficients0381 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (555/8192), (735/16384), (4485/65536)]

def upper0381 : ℚ := (95577/131072000000000)

def plusWeights0381 : Fin 11 → ℚ := ![(95577/131072000000000), (95577/13107200000000), (860193/26214400000000), (286731/3276800000000), (2007117/13107200000000), (6021351/32768000000000), (2007117/13107200000000), (286731/3276800000000), (877953/26214400000000), (4557/524288000000), (95577/65536000000000)]

def minusWeights0381 : Fin 11 → ℚ := ![(95577/131072000000000), (95577/13107200000000), (860193/26214400000000), (286731/3276800000000), (2007117/13107200000000), (6021351/32768000000000), (2007117/13107200000000), (286731/3276800000000), (842433/26214400000000), (77229/13107200000000), 0]

theorem checked0381 :
    (∀ i, 0 ≤ plusWeights0381 i) ∧
    (∀ i, 0 ≤ minusWeights0381 i) ∧
    (∀ i, plusCoefficients coefficients0381 upper0381 i = powerCoefficients10 plusWeights0381 i) ∧
    (∀ i, minusCoefficients coefficients0381 upper0381 i = powerCoefficients10 minusWeights0381 i) := by
  decide +kernel

theorem bound0381 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0381 g| ≤ (upper0381 : ℝ) :=
  abs_of_coefficients coefficients0381 upper0381 powerCoefficients10 plusWeights0381 minusWeights0381
    checked0381.1 checked0381.2.1 checked0381.2.2.1 checked0381.2.2.2
    (power_identity10 plusWeights0381) (power_identity10 minusWeights0381) g hg hmax

def envelope0381 : Envelope := ⟨coefficients0381, upper0381, bound0381⟩

def coefficients0382 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (585/8192), (645/16384), (2745/65536)]

def upper0382 : ℚ := (99309/131072000000000)

def plusWeights0382 : Fin 11 → ℚ := ![(99309/131072000000000), (99309/13107200000000), (893781/26214400000000), (297927/3276800000000), (2085489/13107200000000), (6256467/32768000000000), (2085489/13107200000000), (297927/3276800000000), (912501/26214400000000), (23709/2621440000000), (99309/65536000000000)]

def minusWeights0382 : Fin 11 → ℚ := ![(99309/131072000000000), (99309/13107200000000), (893781/26214400000000), (297927/3276800000000), (2085489/13107200000000), (6256467/32768000000000), (2085489/13107200000000), (297927/3276800000000), (875061/26214400000000), (80073/13107200000000), 0]

theorem checked0382 :
    (∀ i, 0 ≤ plusWeights0382 i) ∧
    (∀ i, 0 ≤ minusWeights0382 i) ∧
    (∀ i, plusCoefficients coefficients0382 upper0382 i = powerCoefficients10 plusWeights0382 i) ∧
    (∀ i, minusCoefficients coefficients0382 upper0382 i = powerCoefficients10 minusWeights0382 i) := by
  decide +kernel

theorem bound0382 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0382 g| ≤ (upper0382 : ℝ) :=
  abs_of_coefficients coefficients0382 upper0382 powerCoefficients10 plusWeights0382 minusWeights0382
    checked0382.1 checked0382.2.1 checked0382.2.2.1 checked0382.2.2.2
    (power_identity10 plusWeights0382) (power_identity10 minusWeights0382) g hg hmax

def envelope0382 : Envelope := ⟨coefficients0382, upper0382, bound0382⟩

def coefficients0383 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (45/512), (45/512), (45/2048)]

def upper0383 : ℚ := (3969/4096000000000)

def plusWeights0383 : Fin 11 → ℚ := ![(3969/4096000000000), (3969/409600000000), (35721/819200000000), (11907/102400000000), (83349/409600000000), (250047/1024000000000), (83349/409600000000), (11907/102400000000), (36441/819200000000), (189/16384000000), (3969/2048000000000)]

def minusWeights0383 : Fin 11 → ℚ := ![(3969/4096000000000), (3969/409600000000), (35721/819200000000), (11907/102400000000), (83349/409600000000), (250047/1024000000000), (83349/409600000000), (11907/102400000000), (35001/819200000000), (3213/409600000000), 0]

theorem checked0383 :
    (∀ i, 0 ≤ plusWeights0383 i) ∧
    (∀ i, 0 ≤ minusWeights0383 i) ∧
    (∀ i, plusCoefficients coefficients0383 upper0383 i = powerCoefficients10 plusWeights0383 i) ∧
    (∀ i, minusCoefficients coefficients0383 upper0383 i = powerCoefficients10 minusWeights0383 i) := by
  decide +kernel

theorem bound0383 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0383 g| ≤ (upper0383 : ℝ) :=
  abs_of_coefficients coefficients0383 upper0383 powerCoefficients10 plusWeights0383 minusWeights0383
    checked0383.1 checked0383.2.1 checked0383.2.2.1 checked0383.2.2.2
    (power_identity10 plusWeights0383) (power_identity10 minusWeights0383) g hg hmax

def envelope0383 : Envelope := ⟨coefficients0383, upper0383, bound0383⟩

end BilayerDressed.CubicQuarticEnvelopes

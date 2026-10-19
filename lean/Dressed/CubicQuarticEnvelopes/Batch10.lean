import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0320 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1125/65536)]

def upper0320 : ℚ := (9/5242880000000)

def plusWeights0320 : Fin 11 → ℚ := ![(9/5242880000000), (9/524288000000), (81/1048576000000), (27/131072000000), (189/524288000000), (567/1310720000000), (189/524288000000), (27/131072000000), (81/1048576000000), (9/524288000000), (9/2621440000000)]

def minusWeights0320 : Fin 11 → ℚ := ![(9/5242880000000), (9/524288000000), (81/1048576000000), (27/131072000000), (189/524288000000), (567/1310720000000), (189/524288000000), (27/131072000000), (81/1048576000000), (9/524288000000), 0]

theorem checked0320 :
    (∀ i, 0 ≤ plusWeights0320 i) ∧
    (∀ i, 0 ≤ minusWeights0320 i) ∧
    (∀ i, plusCoefficients coefficients0320 upper0320 i = powerCoefficients10 plusWeights0320 i) ∧
    (∀ i, minusCoefficients coefficients0320 upper0320 i = powerCoefficients10 minusWeights0320 i) := by
  decide +kernel

theorem bound0320 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0320 g| ≤ (upper0320 : ℝ) :=
  abs_of_coefficients coefficients0320 upper0320 powerCoefficients10 plusWeights0320 minusWeights0320
    checked0320.1 checked0320.2.1 checked0320.2.2.1 checked0320.2.2.2
    (power_identity10 plusWeights0320) (power_identity10 minusWeights0320) g hg hmax

def envelope0320 : Envelope := ⟨coefficients0320, upper0320, bound0320⟩

def coefficients0321 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3375/131072)]

def upper0321 : ℚ := (27/10485760000000)

def plusWeights0321 : Fin 11 → ℚ := ![(27/10485760000000), (27/1048576000000), (243/2097152000000), (81/262144000000), (567/1048576000000), (1701/2621440000000), (567/1048576000000), (81/262144000000), (243/2097152000000), (27/1048576000000), (27/5242880000000)]

def minusWeights0321 : Fin 11 → ℚ := ![(27/10485760000000), (27/1048576000000), (243/2097152000000), (81/262144000000), (567/1048576000000), (1701/2621440000000), (567/1048576000000), (81/262144000000), (243/2097152000000), (27/1048576000000), 0]

theorem checked0321 :
    (∀ i, 0 ≤ plusWeights0321 i) ∧
    (∀ i, 0 ≤ minusWeights0321 i) ∧
    (∀ i, plusCoefficients coefficients0321 upper0321 i = powerCoefficients10 plusWeights0321 i) ∧
    (∀ i, minusCoefficients coefficients0321 upper0321 i = powerCoefficients10 minusWeights0321 i) := by
  decide +kernel

theorem bound0321 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0321 g| ≤ (upper0321 : ℝ) :=
  abs_of_coefficients coefficients0321 upper0321 powerCoefficients10 plusWeights0321 minusWeights0321
    checked0321.1 checked0321.2.1 checked0321.2.2.1 checked0321.2.2.2
    (power_identity10 plusWeights0321) (power_identity10 minusWeights0321) g hg hmax

def envelope0321 : Envelope := ⟨coefficients0321, upper0321, bound0321⟩

def coefficients0322 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1125/32768)]

def upper0322 : ℚ := (9/2621440000000)

def plusWeights0322 : Fin 11 → ℚ := ![(9/2621440000000), (9/262144000000), (81/524288000000), (27/65536000000), (189/262144000000), (567/655360000000), (189/262144000000), (27/65536000000), (81/524288000000), (9/262144000000), (9/1310720000000)]

def minusWeights0322 : Fin 11 → ℚ := ![(9/2621440000000), (9/262144000000), (81/524288000000), (27/65536000000), (189/262144000000), (567/655360000000), (189/262144000000), (27/65536000000), (81/524288000000), (9/262144000000), 0]

theorem checked0322 :
    (∀ i, 0 ≤ plusWeights0322 i) ∧
    (∀ i, 0 ≤ minusWeights0322 i) ∧
    (∀ i, plusCoefficients coefficients0322 upper0322 i = powerCoefficients10 plusWeights0322 i) ∧
    (∀ i, minusCoefficients coefficients0322 upper0322 i = powerCoefficients10 minusWeights0322 i) := by
  decide +kernel

theorem bound0322 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0322 g| ≤ (upper0322 : ℝ) :=
  abs_of_coefficients coefficients0322 upper0322 powerCoefficients10 plusWeights0322 minusWeights0322
    checked0322.1 checked0322.2.1 checked0322.2.2.1 checked0322.2.2.2
    (power_identity10 plusWeights0322) (power_identity10 minusWeights0322) g hg hmax

def envelope0322 : Envelope := ⟨coefficients0322, upper0322, bound0322⟩

def coefficients0323 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (2625/65536)]

def upper0323 : ℚ := (21/5242880000000)

def plusWeights0323 : Fin 11 → ℚ := ![(21/5242880000000), (21/524288000000), (189/1048576000000), (63/131072000000), (441/524288000000), (1323/1310720000000), (441/524288000000), (63/131072000000), (189/1048576000000), (21/524288000000), (21/2621440000000)]

def minusWeights0323 : Fin 11 → ℚ := ![(21/5242880000000), (21/524288000000), (189/1048576000000), (63/131072000000), (441/524288000000), (1323/1310720000000), (441/524288000000), (63/131072000000), (189/1048576000000), (21/524288000000), 0]

theorem checked0323 :
    (∀ i, 0 ≤ plusWeights0323 i) ∧
    (∀ i, 0 ≤ minusWeights0323 i) ∧
    (∀ i, plusCoefficients coefficients0323 upper0323 i = powerCoefficients10 plusWeights0323 i) ∧
    (∀ i, minusCoefficients coefficients0323 upper0323 i = powerCoefficients10 minusWeights0323 i) := by
  decide +kernel

theorem bound0323 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0323 g| ≤ (upper0323 : ℝ) :=
  abs_of_coefficients coefficients0323 upper0323 powerCoefficients10 plusWeights0323 minusWeights0323
    checked0323.1 checked0323.2.1 checked0323.2.2.1 checked0323.2.2.2
    (power_identity10 plusWeights0323) (power_identity10 minusWeights0323) g hg hmax

def envelope0323 : Envelope := ⟨coefficients0323, upper0323, bound0323⟩

def coefficients0324 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/32768), (75/65536), (1875/262144)]

def upper0324 : ℚ := (519/20971520000000)

def plusWeights0324 : Fin 11 → ℚ := ![(519/20971520000000), (519/2097152000000), (4671/4194304000000), (1557/524288000000), (10899/2097152000000), (32697/5242880000000), (10899/2097152000000), (1557/524288000000), (4767/4194304000000), (3087/10485760000000), (519/10485760000000)]

def minusWeights0324 : Fin 11 → ℚ := ![(519/20971520000000), (519/2097152000000), (4671/4194304000000), (1557/524288000000), (10899/2097152000000), (32697/5242880000000), (10899/2097152000000), (1557/524288000000), (183/167772160000), (2103/10485760000000), 0]

theorem checked0324 :
    (∀ i, 0 ≤ plusWeights0324 i) ∧
    (∀ i, 0 ≤ minusWeights0324 i) ∧
    (∀ i, plusCoefficients coefficients0324 upper0324 i = powerCoefficients10 plusWeights0324 i) ∧
    (∀ i, minusCoefficients coefficients0324 upper0324 i = powerCoefficients10 minusWeights0324 i) := by
  decide +kernel

theorem bound0324 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0324 g| ≤ (upper0324 : ℝ) :=
  abs_of_coefficients coefficients0324 upper0324 powerCoefficients10 plusWeights0324 minusWeights0324
    checked0324.1 checked0324.2.1 checked0324.2.2.1 checked0324.2.2.2
    (power_identity10 plusWeights0324) (power_identity10 minusWeights0324) g hg hmax

def envelope0324 : Envelope := ⟨coefficients0324, upper0324, bound0324⟩

def coefficients0325 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (5/2048), (5/2048), (5/8192)]

def upper0325 : ℚ := (441/16384000000000)

def plusWeights0325 : Fin 11 → ℚ := ![(441/16384000000000), (441/1638400000000), (3969/3276800000000), (1323/409600000000), (9261/1638400000000), (27783/4096000000000), (9261/1638400000000), (1323/409600000000), (4049/3276800000000), (21/65536000000), (441/8192000000000)]

def minusWeights0325 : Fin 11 → ℚ := ![(441/16384000000000), (441/1638400000000), (3969/3276800000000), (1323/409600000000), (9261/1638400000000), (27783/4096000000000), (9261/1638400000000), (1323/409600000000), (3889/3276800000000), (357/1638400000000), 0]

theorem checked0325 :
    (∀ i, 0 ≤ plusWeights0325 i) ∧
    (∀ i, 0 ≤ minusWeights0325 i) ∧
    (∀ i, plusCoefficients coefficients0325 upper0325 i = powerCoefficients10 plusWeights0325 i) ∧
    (∀ i, minusCoefficients coefficients0325 upper0325 i = powerCoefficients10 minusWeights0325 i) := by
  decide +kernel

theorem bound0325 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0325 g| ≤ (upper0325 : ℝ) :=
  abs_of_coefficients coefficients0325 upper0325 powerCoefficients10 plusWeights0325 minusWeights0325
    checked0325.1 checked0325.2.1 checked0325.2.2.1 checked0325.2.2.2
    (power_identity10 plusWeights0325) (power_identity10 minusWeights0325) g hg hmax

def envelope0325 : Envelope := ⟨coefficients0325, upper0325, bound0325⟩

def coefficients0326 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (45/16384), (65/32768), (135/32768)]

def upper0326 : ℚ := (1957/65536000000000)

def plusWeights0326 : Fin 11 → ℚ := ![(1957/65536000000000), (1957/6553600000000), (17613/13107200000000), (5871/1638400000000), (41097/6553600000000), (123291/16384000000000), (41097/6553600000000), (5871/1638400000000), (17973/13107200000000), (233/655360000000), (1957/32768000000000)]

def minusWeights0326 : Fin 11 → ℚ := ![(1957/65536000000000), (1957/6553600000000), (17613/13107200000000), (5871/1638400000000), (41097/6553600000000), (123291/16384000000000), (41097/6553600000000), (5871/1638400000000), (17253/13107200000000), (99/409600000000), 0]

theorem checked0326 :
    (∀ i, 0 ≤ plusWeights0326 i) ∧
    (∀ i, 0 ≤ minusWeights0326 i) ∧
    (∀ i, plusCoefficients coefficients0326 upper0326 i = powerCoefficients10 plusWeights0326 i) ∧
    (∀ i, minusCoefficients coefficients0326 upper0326 i = powerCoefficients10 minusWeights0326 i) := by
  decide +kernel

theorem bound0326 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0326 g| ≤ (upper0326 : ℝ) :=
  abs_of_coefficients coefficients0326 upper0326 powerCoefficients10 plusWeights0326 minusWeights0326
    checked0326.1 checked0326.2.1 checked0326.2.2.1 checked0326.2.2.2
    (power_identity10 plusWeights0326) (power_identity10 minusWeights0326) g hg hmax

def envelope0326 : Envelope := ⟨coefficients0326, upper0326, bound0326⟩

def coefficients0327 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (25/8192), (25/16384), (625/131072)]

def upper0327 : ℚ := (341/10485760000000)

def plusWeights0327 : Fin 11 → ℚ := ![(341/10485760000000), (341/1048576000000), (3069/2097152000000), (1023/262144000000), (7161/1048576000000), (21483/2621440000000), (7161/1048576000000), (1023/262144000000), (3133/2097152000000), (2033/5242880000000), (341/5242880000000)]

def minusWeights0327 : Fin 11 → ℚ := ![(341/10485760000000), (341/1048576000000), (3069/2097152000000), (1023/262144000000), (7161/1048576000000), (21483/2621440000000), (7161/1048576000000), (1023/262144000000), (601/419430400000), (1377/5242880000000), 0]

theorem checked0327 :
    (∀ i, 0 ≤ plusWeights0327 i) ∧
    (∀ i, 0 ≤ minusWeights0327 i) ∧
    (∀ i, plusCoefficients coefficients0327 upper0327 i = powerCoefficients10 plusWeights0327 i) ∧
    (∀ i, minusCoefficients coefficients0327 upper0327 i = powerCoefficients10 minusWeights0327 i) := by
  decide +kernel

theorem bound0327 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0327 g| ≤ (upper0327 : ℝ) :=
  abs_of_coefficients coefficients0327 upper0327 powerCoefficients10 plusWeights0327 minusWeights0327
    checked0327.1 checked0327.2.1 checked0327.2.2.1 checked0327.2.2.2
    (power_identity10 plusWeights0327) (power_identity10 minusWeights0327) g hg hmax

def envelope0327 : Envelope := ⟨coefficients0327, upper0327, bound0327⟩

def coefficients0328 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (15/4096), (15/4096), (15/16384)]

def upper0328 : ℚ := (1323/32768000000000)

def plusWeights0328 : Fin 11 → ℚ := ![(1323/32768000000000), (1323/3276800000000), (11907/6553600000000), (3969/819200000000), (27783/3276800000000), (83349/8192000000000), (27783/3276800000000), (3969/819200000000), (12147/6553600000000), (63/131072000000), (1323/16384000000000)]

def minusWeights0328 : Fin 11 → ℚ := ![(1323/32768000000000), (1323/3276800000000), (11907/6553600000000), (3969/819200000000), (27783/3276800000000), (83349/8192000000000), (27783/3276800000000), (3969/819200000000), (11667/6553600000000), (1071/3276800000000), 0]

theorem checked0328 :
    (∀ i, 0 ≤ plusWeights0328 i) ∧
    (∀ i, 0 ≤ minusWeights0328 i) ∧
    (∀ i, plusCoefficients coefficients0328 upper0328 i = powerCoefficients10 plusWeights0328 i) ∧
    (∀ i, minusCoefficients coefficients0328 upper0328 i = powerCoefficients10 minusWeights0328 i) := by
  decide +kernel

theorem bound0328 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0328 g| ≤ (upper0328 : ℝ) :=
  abs_of_coefficients coefficients0328 upper0328 powerCoefficients10 plusWeights0328 minusWeights0328
    checked0328.1 checked0328.2.1 checked0328.2.2.1 checked0328.2.2.2
    (power_identity10 plusWeights0328) (power_identity10 minusWeights0328) g hg hmax

def envelope0328 : Envelope := ⟨coefficients0328, upper0328, bound0328⟩

def coefficients0329 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/16384), (75/32768), (125/65536)]

def upper0329 : ℚ := (253/5242880000000)

def plusWeights0329 : Fin 11 → ℚ := ![(253/5242880000000), (253/524288000000), (2277/1048576000000), (759/131072000000), (5313/524288000000), (15939/1310720000000), (5313/524288000000), (759/131072000000), (93/41943040000), (1511/2621440000000), (253/2621440000000)]

def minusWeights0329 : Fin 11 → ℚ := ![(253/5242880000000), (253/524288000000), (2277/1048576000000), (759/131072000000), (5313/524288000000), (15939/1310720000000), (5313/524288000000), (759/131072000000), (2229/1048576000000), (1019/2621440000000), 0]

theorem checked0329 :
    (∀ i, 0 ≤ plusWeights0329 i) ∧
    (∀ i, 0 ≤ minusWeights0329 i) ∧
    (∀ i, plusCoefficients coefficients0329 upper0329 i = powerCoefficients10 plusWeights0329 i) ∧
    (∀ i, minusCoefficients coefficients0329 upper0329 i = powerCoefficients10 minusWeights0329 i) := by
  decide +kernel

theorem bound0329 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0329 g| ≤ (upper0329 : ℝ) :=
  abs_of_coefficients coefficients0329 upper0329 powerCoefficients10 plusWeights0329 minusWeights0329
    checked0329.1 checked0329.2.1 checked0329.2.2.1 checked0329.2.2.2
    (power_identity10 plusWeights0329) (power_identity10 minusWeights0329) g hg hmax

def envelope0329 : Envelope := ⟨coefficients0329, upper0329, bound0329⟩

def coefficients0330 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/16384), (75/32768), (375/131072)]

def upper0330 : ℚ := (507/10485760000000)

def plusWeights0330 : Fin 11 → ℚ := ![(507/10485760000000), (507/1048576000000), (4563/2097152000000), (1521/262144000000), (10647/1048576000000), (31941/2621440000000), (10647/1048576000000), (1521/262144000000), (4659/2097152000000), (3027/5242880000000), (507/5242880000000)]

def minusWeights0330 : Fin 11 → ℚ := ![(507/10485760000000), (507/1048576000000), (4563/2097152000000), (1521/262144000000), (10647/1048576000000), (31941/2621440000000), (10647/1048576000000), (1521/262144000000), (4467/2097152000000), (2043/5242880000000), 0]

theorem checked0330 :
    (∀ i, 0 ≤ plusWeights0330 i) ∧
    (∀ i, 0 ≤ minusWeights0330 i) ∧
    (∀ i, plusCoefficients coefficients0330 upper0330 i = powerCoefficients10 plusWeights0330 i) ∧
    (∀ i, minusCoefficients coefficients0330 upper0330 i = powerCoefficients10 minusWeights0330 i) := by
  decide +kernel

theorem bound0330 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0330 g| ≤ (upper0330 : ℝ) :=
  abs_of_coefficients coefficients0330 upper0330 powerCoefficients10 plusWeights0330 minusWeights0330
    checked0330.1 checked0330.2.1 checked0330.2.2.1 checked0330.2.2.2
    (power_identity10 plusWeights0330) (power_identity10 minusWeights0330) g hg hmax

def envelope0330 : Envelope := ⟨coefficients0330, upper0330, bound0330⟩

def coefficients0331 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/16384), (75/32768), (1875/65536)]

def upper0331 : ℚ := (267/5242880000000)

def plusWeights0331 : Fin 11 → ℚ := ![(267/5242880000000), (267/524288000000), (2403/1048576000000), (801/131072000000), (5607/524288000000), (16821/1310720000000), (5607/524288000000), (801/131072000000), (2451/1048576000000), (1581/2621440000000), (267/2621440000000)]

def minusWeights0331 : Fin 11 → ℚ := ![(267/5242880000000), (267/524288000000), (2403/1048576000000), (801/131072000000), (5607/524288000000), (16821/1310720000000), (5607/524288000000), (801/131072000000), (471/209715200000), (1089/2621440000000), 0]

theorem checked0331 :
    (∀ i, 0 ≤ plusWeights0331 i) ∧
    (∀ i, 0 ≤ minusWeights0331 i) ∧
    (∀ i, plusCoefficients coefficients0331 upper0331 i = powerCoefficients10 plusWeights0331 i) ∧
    (∀ i, minusCoefficients coefficients0331 upper0331 i = powerCoefficients10 minusWeights0331 i) := by
  decide +kernel

theorem bound0331 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0331 g| ≤ (upper0331 : ℝ) :=
  abs_of_coefficients coefficients0331 upper0331 powerCoefficients10 plusWeights0331 minusWeights0331
    checked0331.1 checked0331.2.1 checked0331.2.2.1 checked0331.2.2.2
    (power_identity10 plusWeights0331) (power_identity10 minusWeights0331) g hg hmax

def envelope0331 : Envelope := ⟨coefficients0331, upper0331, bound0331⟩

def coefficients0332 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (5/1024), (5/1024), (5/4096)]

def upper0332 : ℚ := (441/8192000000000)

def plusWeights0332 : Fin 11 → ℚ := ![(441/8192000000000), (441/819200000000), (3969/1638400000000), (1323/204800000000), (9261/819200000000), (27783/2048000000000), (9261/819200000000), (1323/204800000000), (4049/1638400000000), (21/32768000000), (441/4096000000000)]

def minusWeights0332 : Fin 11 → ℚ := ![(441/8192000000000), (441/819200000000), (3969/1638400000000), (1323/204800000000), (9261/819200000000), (27783/2048000000000), (9261/819200000000), (1323/204800000000), (3889/1638400000000), (357/819200000000), 0]

theorem checked0332 :
    (∀ i, 0 ≤ plusWeights0332 i) ∧
    (∀ i, 0 ≤ minusWeights0332 i) ∧
    (∀ i, plusCoefficients coefficients0332 upper0332 i = powerCoefficients10 plusWeights0332 i) ∧
    (∀ i, minusCoefficients coefficients0332 upper0332 i = powerCoefficients10 minusWeights0332 i) := by
  decide +kernel

theorem bound0332 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0332 g| ≤ (upper0332 : ℝ) :=
  abs_of_coefficients coefficients0332 upper0332 powerCoefficients10 plusWeights0332 minusWeights0332
    checked0332.1 checked0332.2.1 checked0332.2.2.1 checked0332.2.2.2
    (power_identity10 plusWeights0332) (power_identity10 minusWeights0332) g hg hmax

def envelope0332 : Envelope := ⟨coefficients0332, upper0332, bound0332⟩

def coefficients0333 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (25/4096), (25/8192), (125/32768)]

def upper0333 : ℚ := (169/2621440000000)

def plusWeights0333 : Fin 11 → ℚ := ![(169/2621440000000), (169/262144000000), (1521/524288000000), (507/65536000000), (3549/262144000000), (10647/655360000000), (3549/262144000000), (507/65536000000), (1553/524288000000), (1009/1310720000000), (169/1310720000000)]

def minusWeights0333 : Fin 11 → ℚ := ![(169/2621440000000), (169/262144000000), (1521/524288000000), (507/65536000000), (3549/262144000000), (10647/655360000000), (3549/262144000000), (507/65536000000), (1489/524288000000), (681/1310720000000), 0]

theorem checked0333 :
    (∀ i, 0 ≤ plusWeights0333 i) ∧
    (∀ i, 0 ≤ minusWeights0333 i) ∧
    (∀ i, plusCoefficients coefficients0333 upper0333 i = powerCoefficients10 plusWeights0333 i) ∧
    (∀ i, minusCoefficients coefficients0333 upper0333 i = powerCoefficients10 minusWeights0333 i) := by
  decide +kernel

theorem bound0333 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0333 g| ≤ (upper0333 : ℝ) :=
  abs_of_coefficients coefficients0333 upper0333 powerCoefficients10 plusWeights0333 minusWeights0333
    checked0333.1 checked0333.2.1 checked0333.2.2.1 checked0333.2.2.2
    (power_identity10 plusWeights0333) (power_identity10 minusWeights0333) g hg hmax

def envelope0333 : Envelope := ⟨coefficients0333, upper0333, bound0333⟩

def coefficients0334 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (25/4096), (25/4096), (25/16384)]

def upper0334 : ℚ := (441/6553600000000)

def plusWeights0334 : Fin 11 → ℚ := ![(441/6553600000000), (441/655360000000), (3969/1310720000000), (1323/163840000000), (9261/655360000000), (27783/1638400000000), (9261/655360000000), (1323/163840000000), (4049/1310720000000), (21/26214400000), (441/3276800000000)]

def minusWeights0334 : Fin 11 → ℚ := ![(441/6553600000000), (441/655360000000), (3969/1310720000000), (1323/163840000000), (9261/655360000000), (27783/1638400000000), (9261/655360000000), (1323/163840000000), (3889/1310720000000), (357/655360000000), 0]

theorem checked0334 :
    (∀ i, 0 ≤ plusWeights0334 i) ∧
    (∀ i, 0 ≤ minusWeights0334 i) ∧
    (∀ i, plusCoefficients coefficients0334 upper0334 i = powerCoefficients10 plusWeights0334 i) ∧
    (∀ i, minusCoefficients coefficients0334 upper0334 i = powerCoefficients10 minusWeights0334 i) := by
  decide +kernel

theorem bound0334 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0334 g| ≤ (upper0334 : ℝ) :=
  abs_of_coefficients coefficients0334 upper0334 powerCoefficients10 plusWeights0334 minusWeights0334
    checked0334.1 checked0334.2.1 checked0334.2.2.1 checked0334.2.2.2
    (power_identity10 plusWeights0334) (power_identity10 minusWeights0334) g hg hmax

def envelope0334 : Envelope := ⟨coefficients0334, upper0334, bound0334⟩

def coefficients0335 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (225/32768), (225/65536), (1125/262144)]

def upper0335 : ℚ := (1521/20971520000000)

def plusWeights0335 : Fin 11 → ℚ := ![(1521/20971520000000), (1521/2097152000000), (13689/4194304000000), (4563/524288000000), (31941/2097152000000), (95823/5242880000000), (31941/2097152000000), (4563/524288000000), (13977/4194304000000), (9081/10485760000000), (1521/10485760000000)]

def minusWeights0335 : Fin 11 → ℚ := ![(1521/20971520000000), (1521/2097152000000), (13689/4194304000000), (4563/524288000000), (31941/2097152000000), (95823/5242880000000), (31941/2097152000000), (4563/524288000000), (13401/4194304000000), (6129/10485760000000), 0]

theorem checked0335 :
    (∀ i, 0 ≤ plusWeights0335 i) ∧
    (∀ i, 0 ≤ minusWeights0335 i) ∧
    (∀ i, plusCoefficients coefficients0335 upper0335 i = powerCoefficients10 plusWeights0335 i) ∧
    (∀ i, minusCoefficients coefficients0335 upper0335 i = powerCoefficients10 minusWeights0335 i) := by
  decide +kernel

theorem bound0335 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0335 g| ≤ (upper0335 : ℝ) :=
  abs_of_coefficients coefficients0335 upper0335 powerCoefficients10 plusWeights0335 minusWeights0335
    checked0335.1 checked0335.2.1 checked0335.2.2.1 checked0335.2.2.2
    (power_identity10 plusWeights0335) (power_identity10 minusWeights0335) g hg hmax

def envelope0335 : Envelope := ⟨coefficients0335, upper0335, bound0335⟩

def coefficients0336 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (225/32768), (225/65536), (16125/262144)]

def upper0336 : ℚ := (1641/20971520000000)

def plusWeights0336 : Fin 11 → ℚ := ![(1641/20971520000000), (1641/2097152000000), (14769/4194304000000), (4923/524288000000), (34461/2097152000000), (103383/5242880000000), (34461/2097152000000), (4923/524288000000), (15057/4194304000000), (9681/10485760000000), (1641/10485760000000)]

def minusWeights0336 : Fin 11 → ℚ := ![(1641/20971520000000), (1641/2097152000000), (14769/4194304000000), (4923/524288000000), (34461/2097152000000), (103383/5242880000000), (34461/2097152000000), (4923/524288000000), (14481/4194304000000), (6729/10485760000000), 0]

theorem checked0336 :
    (∀ i, 0 ≤ plusWeights0336 i) ∧
    (∀ i, 0 ≤ minusWeights0336 i) ∧
    (∀ i, plusCoefficients coefficients0336 upper0336 i = powerCoefficients10 plusWeights0336 i) ∧
    (∀ i, minusCoefficients coefficients0336 upper0336 i = powerCoefficients10 minusWeights0336 i) := by
  decide +kernel

theorem bound0336 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0336 g| ≤ (upper0336 : ℝ) :=
  abs_of_coefficients coefficients0336 upper0336 powerCoefficients10 plusWeights0336 minusWeights0336
    checked0336.1 checked0336.2.1 checked0336.2.2.1 checked0336.2.2.2
    (power_identity10 plusWeights0336) (power_identity10 minusWeights0336) g hg hmax

def envelope0336 : Envelope := ⟨coefficients0336, upper0336, bound0336⟩

def coefficients0337 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (225/32768), (325/65536), (1225/131072)]

def upper0337 : ℚ := (3909/52428800000000)

def plusWeights0337 : Fin 11 → ℚ := ![(3909/52428800000000), (3909/5242880000000), (35181/10485760000000), (11727/1310720000000), (82089/5242880000000), (246267/13107200000000), (82089/5242880000000), (11727/1310720000000), (35901/10485760000000), (931/1048576000000), (3909/26214400000000)]

def minusWeights0337 : Fin 11 → ℚ := ![(3909/52428800000000), (3909/5242880000000), (35181/10485760000000), (11727/1310720000000), (82089/5242880000000), (246267/13107200000000), (82089/5242880000000), (11727/1310720000000), (34461/10485760000000), (3163/5242880000000), 0]

theorem checked0337 :
    (∀ i, 0 ≤ plusWeights0337 i) ∧
    (∀ i, 0 ≤ minusWeights0337 i) ∧
    (∀ i, plusCoefficients coefficients0337 upper0337 i = powerCoefficients10 plusWeights0337 i) ∧
    (∀ i, minusCoefficients coefficients0337 upper0337 i = powerCoefficients10 minusWeights0337 i) := by
  decide +kernel

theorem bound0337 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0337 g| ≤ (upper0337 : ℝ) :=
  abs_of_coefficients coefficients0337 upper0337 powerCoefficients10 plusWeights0337 minusWeights0337
    checked0337.1 checked0337.2.1 checked0337.2.2.1 checked0337.2.2.2
    (power_identity10 plusWeights0337) (power_identity10 minusWeights0337) g hg hmax

def envelope0337 : Envelope := ⟨coefficients0337, upper0337, bound0337⟩

def coefficients0338 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (235/32768), (295/65536), (935/131072)]

def upper0338 : ℚ := (20167/262144000000000)

def plusWeights0338 : Fin 11 → ℚ := ![(20167/262144000000000), (20167/26214400000000), (181503/52428800000000), (60501/6553600000000), (423507/26214400000000), (1270521/65536000000000), (423507/26214400000000), (60501/6553600000000), (185263/52428800000000), (4809/5242880000000), (20167/131072000000000)]

def minusWeights0338 : Fin 11 → ℚ := ![(20167/262144000000000), (20167/26214400000000), (181503/52428800000000), (60501/6553600000000), (423507/26214400000000), (1270521/65536000000000), (423507/26214400000000), (60501/6553600000000), (177743/52428800000000), (16289/26214400000000), 0]

theorem checked0338 :
    (∀ i, 0 ≤ plusWeights0338 i) ∧
    (∀ i, 0 ≤ minusWeights0338 i) ∧
    (∀ i, plusCoefficients coefficients0338 upper0338 i = powerCoefficients10 plusWeights0338 i) ∧
    (∀ i, minusCoefficients coefficients0338 upper0338 i = powerCoefficients10 minusWeights0338 i) := by
  decide +kernel

theorem bound0338 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0338 g| ≤ (upper0338 : ℝ) :=
  abs_of_coefficients coefficients0338 upper0338 powerCoefficients10 plusWeights0338 minusWeights0338
    checked0338.1 checked0338.2.1 checked0338.2.2.1 checked0338.2.2.2
    (power_identity10 plusWeights0338) (power_identity10 minusWeights0338) g hg hmax

def envelope0338 : Envelope := ⟨coefficients0338, upper0338, bound0338⟩

def coefficients0339 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (15/2048), (15/2048), (15/8192)]

def upper0339 : ℚ := (1323/16384000000000)

def plusWeights0339 : Fin 11 → ℚ := ![(1323/16384000000000), (1323/1638400000000), (11907/3276800000000), (3969/409600000000), (27783/1638400000000), (83349/4096000000000), (27783/1638400000000), (3969/409600000000), (12147/3276800000000), (63/65536000000), (1323/8192000000000)]

def minusWeights0339 : Fin 11 → ℚ := ![(1323/16384000000000), (1323/1638400000000), (11907/3276800000000), (3969/409600000000), (27783/1638400000000), (83349/4096000000000), (27783/1638400000000), (3969/409600000000), (11667/3276800000000), (1071/1638400000000), 0]

theorem checked0339 :
    (∀ i, 0 ≤ plusWeights0339 i) ∧
    (∀ i, 0 ≤ minusWeights0339 i) ∧
    (∀ i, plusCoefficients coefficients0339 upper0339 i = powerCoefficients10 plusWeights0339 i) ∧
    (∀ i, minusCoefficients coefficients0339 upper0339 i = powerCoefficients10 minusWeights0339 i) := by
  decide +kernel

theorem bound0339 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0339 g| ≤ (upper0339 : ℝ) :=
  abs_of_coefficients coefficients0339 upper0339 powerCoefficients10 plusWeights0339 minusWeights0339
    checked0339.1 checked0339.2.1 checked0339.2.2.1 checked0339.2.2.2
    (power_identity10 plusWeights0339) (power_identity10 minusWeights0339) g hg hmax

def envelope0339 : Envelope := ⟨coefficients0339, upper0339, bound0339⟩

def coefficients0340 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/16384), (195/32768), (1245/131072)]

def upper0340 : ℚ := (23409/262144000000000)

def plusWeights0340 : Fin 11 → ℚ := ![(23409/262144000000000), (23409/26214400000000), (210681/52428800000000), (70227/6553600000000), (491589/26214400000000), (1474767/65536000000000), (491589/26214400000000), (70227/6553600000000), (215001/52428800000000), (5577/5242880000000), (23409/131072000000000)]

def minusWeights0340 : Fin 11 → ℚ := ![(23409/262144000000000), (23409/26214400000000), (210681/52428800000000), (70227/6553600000000), (491589/26214400000000), (1474767/65536000000000), (491589/26214400000000), (70227/6553600000000), (206361/52428800000000), (18933/26214400000000), 0]

theorem checked0340 :
    (∀ i, 0 ≤ plusWeights0340 i) ∧
    (∀ i, 0 ≤ minusWeights0340 i) ∧
    (∀ i, plusCoefficients coefficients0340 upper0340 i = powerCoefficients10 plusWeights0340 i) ∧
    (∀ i, minusCoefficients coefficients0340 upper0340 i = powerCoefficients10 minusWeights0340 i) := by
  decide +kernel

theorem bound0340 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0340 g| ≤ (upper0340 : ℝ) :=
  abs_of_coefficients coefficients0340 upper0340 powerCoefficients10 plusWeights0340 minusWeights0340
    checked0340.1 checked0340.2.1 checked0340.2.2.1 checked0340.2.2.2
    (power_identity10 plusWeights0340) (power_identity10 minusWeights0340) g hg hmax

def envelope0340 : Envelope := ⟨coefficients0340, upper0340, bound0340⟩

def coefficients0341 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/16384), (195/32768), (405/32768)]

def upper0341 : ℚ := (5871/65536000000000)

def plusWeights0341 : Fin 11 → ℚ := ![(5871/65536000000000), (5871/6553600000000), (52839/13107200000000), (17613/1638400000000), (123291/6553600000000), (369873/16384000000000), (123291/6553600000000), (17613/1638400000000), (53919/13107200000000), (699/655360000000), (5871/32768000000000)]

def minusWeights0341 : Fin 11 → ℚ := ![(5871/65536000000000), (5871/6553600000000), (52839/13107200000000), (17613/1638400000000), (123291/6553600000000), (369873/16384000000000), (123291/6553600000000), (17613/1638400000000), (51759/13107200000000), (297/409600000000), 0]

theorem checked0341 :
    (∀ i, 0 ≤ plusWeights0341 i) ∧
    (∀ i, 0 ≤ minusWeights0341 i) ∧
    (∀ i, plusCoefficients coefficients0341 upper0341 i = powerCoefficients10 plusWeights0341 i) ∧
    (∀ i, minusCoefficients coefficients0341 upper0341 i = powerCoefficients10 minusWeights0341 i) := by
  decide +kernel

theorem bound0341 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0341 g| ≤ (upper0341 : ℝ) :=
  abs_of_coefficients coefficients0341 upper0341 powerCoefficients10 plusWeights0341 minusWeights0341
    checked0341.1 checked0341.2.1 checked0341.2.2.1 checked0341.2.2.2
    (power_identity10 plusWeights0341) (power_identity10 minusWeights0341) g hg hmax

def envelope0341 : Envelope := ⟨coefficients0341, upper0341, bound0341⟩

def coefficients0342 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/16384), (195/32768), (1995/131072)]

def upper0342 : ℚ := (23559/262144000000000)

def plusWeights0342 : Fin 11 → ℚ := ![(23559/262144000000000), (23559/26214400000000), (212031/52428800000000), (70677/6553600000000), (494739/26214400000000), (1484217/65536000000000), (494739/26214400000000), (70677/6553600000000), (216351/52428800000000), (5607/5242880000000), (23559/131072000000000)]

def minusWeights0342 : Fin 11 → ℚ := ![(23559/262144000000000), (23559/26214400000000), (212031/52428800000000), (70677/6553600000000), (494739/26214400000000), (1484217/65536000000000), (494739/26214400000000), (70677/6553600000000), (207711/52428800000000), (19083/26214400000000), 0]

theorem checked0342 :
    (∀ i, 0 ≤ plusWeights0342 i) ∧
    (∀ i, 0 ≤ minusWeights0342 i) ∧
    (∀ i, plusCoefficients coefficients0342 upper0342 i = powerCoefficients10 plusWeights0342 i) ∧
    (∀ i, minusCoefficients coefficients0342 upper0342 i = powerCoefficients10 minusWeights0342 i) := by
  decide +kernel

theorem bound0342 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0342 g| ≤ (upper0342 : ℝ) :=
  abs_of_coefficients coefficients0342 upper0342 powerCoefficients10 plusWeights0342 minusWeights0342
    checked0342.1 checked0342.2.1 checked0342.2.2.1 checked0342.2.2.2
    (power_identity10 plusWeights0342) (power_identity10 minusWeights0342) g hg hmax

def envelope0342 : Envelope := ⟨coefficients0342, upper0342, bound0342⟩

def coefficients0343 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/16384), (195/32768), (2745/131072)]

def upper0343 : ℚ := (23709/262144000000000)

def plusWeights0343 : Fin 11 → ℚ := ![(23709/262144000000000), (23709/26214400000000), (213381/52428800000000), (71127/6553600000000), (497889/26214400000000), (1493667/65536000000000), (497889/26214400000000), (71127/6553600000000), (217701/52428800000000), (5637/5242880000000), (23709/131072000000000)]

def minusWeights0343 : Fin 11 → ℚ := ![(23709/262144000000000), (23709/26214400000000), (213381/52428800000000), (71127/6553600000000), (497889/26214400000000), (1493667/65536000000000), (497889/26214400000000), (71127/6553600000000), (209061/52428800000000), (19233/26214400000000), 0]

theorem checked0343 :
    (∀ i, 0 ≤ plusWeights0343 i) ∧
    (∀ i, 0 ≤ minusWeights0343 i) ∧
    (∀ i, plusCoefficients coefficients0343 upper0343 i = powerCoefficients10 plusWeights0343 i) ∧
    (∀ i, minusCoefficients coefficients0343 upper0343 i = powerCoefficients10 minusWeights0343 i) := by
  decide +kernel

theorem bound0343 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0343 g| ≤ (upper0343 : ℝ) :=
  abs_of_coefficients coefficients0343 upper0343 powerCoefficients10 plusWeights0343 minusWeights0343
    checked0343.1 checked0343.2.1 checked0343.2.2.1 checked0343.2.2.2
    (power_identity10 plusWeights0343) (power_identity10 minusWeights0343) g hg hmax

def envelope0343 : Envelope := ⟨coefficients0343, upper0343, bound0343⟩

def coefficients0344 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/16384), (195/32768), (3495/131072)]

def upper0344 : ℚ := (23859/262144000000000)

def plusWeights0344 : Fin 11 → ℚ := ![(23859/262144000000000), (23859/26214400000000), (214731/52428800000000), (71577/6553600000000), (501039/26214400000000), (1503117/65536000000000), (501039/26214400000000), (71577/6553600000000), (219051/52428800000000), (5667/5242880000000), (23859/131072000000000)]

def minusWeights0344 : Fin 11 → ℚ := ![(23859/262144000000000), (23859/26214400000000), (214731/52428800000000), (71577/6553600000000), (501039/26214400000000), (1503117/65536000000000), (501039/26214400000000), (71577/6553600000000), (210411/52428800000000), (19383/26214400000000), 0]

theorem checked0344 :
    (∀ i, 0 ≤ plusWeights0344 i) ∧
    (∀ i, 0 ≤ minusWeights0344 i) ∧
    (∀ i, plusCoefficients coefficients0344 upper0344 i = powerCoefficients10 plusWeights0344 i) ∧
    (∀ i, minusCoefficients coefficients0344 upper0344 i = powerCoefficients10 minusWeights0344 i) := by
  decide +kernel

theorem bound0344 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0344 g| ≤ (upper0344 : ℝ) :=
  abs_of_coefficients coefficients0344 upper0344 powerCoefficients10 plusWeights0344 minusWeights0344
    checked0344.1 checked0344.2.1 checked0344.2.2.1 checked0344.2.2.2
    (power_identity10 plusWeights0344) (power_identity10 minusWeights0344) g hg hmax

def envelope0344 : Envelope := ⟨coefficients0344, upper0344, bound0344⟩

def coefficients0345 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/8192), (75/16384), (375/131072)]

def upper0345 : ℚ := (1011/10485760000000)

def plusWeights0345 : Fin 11 → ℚ := ![(1011/10485760000000), (1011/1048576000000), (9099/2097152000000), (3033/262144000000), (21231/1048576000000), (63693/2621440000000), (21231/1048576000000), (3033/262144000000), (9291/2097152000000), (6039/5242880000000), (1011/5242880000000)]

def minusWeights0345 : Fin 11 → ℚ := ![(1011/10485760000000), (1011/1048576000000), (9099/2097152000000), (3033/262144000000), (21231/1048576000000), (63693/2621440000000), (21231/1048576000000), (3033/262144000000), (8907/2097152000000), (4071/5242880000000), 0]

theorem checked0345 :
    (∀ i, 0 ≤ plusWeights0345 i) ∧
    (∀ i, 0 ≤ minusWeights0345 i) ∧
    (∀ i, plusCoefficients coefficients0345 upper0345 i = powerCoefficients10 plusWeights0345 i) ∧
    (∀ i, minusCoefficients coefficients0345 upper0345 i = powerCoefficients10 minusWeights0345 i) := by
  decide +kernel

theorem bound0345 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0345 g| ≤ (upper0345 : ℝ) :=
  abs_of_coefficients coefficients0345 upper0345 powerCoefficients10 plusWeights0345 minusWeights0345
    checked0345.1 checked0345.2.1 checked0345.2.2.1 checked0345.2.2.2
    (power_identity10 plusWeights0345) (power_identity10 minusWeights0345) g hg hmax

def envelope0345 : Envelope := ⟨coefficients0345, upper0345, bound0345⟩

def coefficients0346 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/8192), (75/16384), (375/65536)]

def upper0346 : ℚ := (507/5242880000000)

def plusWeights0346 : Fin 11 → ℚ := ![(507/5242880000000), (507/524288000000), (4563/1048576000000), (1521/131072000000), (10647/524288000000), (31941/1310720000000), (10647/524288000000), (1521/131072000000), (4659/1048576000000), (3027/2621440000000), (507/2621440000000)]

def minusWeights0346 : Fin 11 → ℚ := ![(507/5242880000000), (507/524288000000), (4563/1048576000000), (1521/131072000000), (10647/524288000000), (31941/1310720000000), (10647/524288000000), (1521/131072000000), (4467/1048576000000), (2043/2621440000000), 0]

theorem checked0346 :
    (∀ i, 0 ≤ plusWeights0346 i) ∧
    (∀ i, 0 ≤ minusWeights0346 i) ∧
    (∀ i, plusCoefficients coefficients0346 upper0346 i = powerCoefficients10 plusWeights0346 i) ∧
    (∀ i, minusCoefficients coefficients0346 upper0346 i = powerCoefficients10 minusWeights0346 i) := by
  decide +kernel

theorem bound0346 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0346 g| ≤ (upper0346 : ℝ) :=
  abs_of_coefficients coefficients0346 upper0346 powerCoefficients10 plusWeights0346 minusWeights0346
    checked0346.1 checked0346.2.1 checked0346.2.2.1 checked0346.2.2.2
    (power_identity10 plusWeights0346) (power_identity10 minusWeights0346) g hg hmax

def envelope0346 : Envelope := ⟨coefficients0346, upper0346, bound0346⟩

def coefficients0347 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/8192), (75/16384), (1875/131072)]

def upper0347 : ℚ := (1023/10485760000000)

def plusWeights0347 : Fin 11 → ℚ := ![(1023/10485760000000), (1023/1048576000000), (9207/2097152000000), (3069/262144000000), (21483/1048576000000), (64449/2621440000000), (21483/1048576000000), (3069/262144000000), (9399/2097152000000), (6099/5242880000000), (1023/5242880000000)]

def minusWeights0347 : Fin 11 → ℚ := ![(1023/10485760000000), (1023/1048576000000), (9207/2097152000000), (3069/262144000000), (21483/1048576000000), (64449/2621440000000), (21483/1048576000000), (3069/262144000000), (1803/419430400000), (4131/5242880000000), 0]

theorem checked0347 :
    (∀ i, 0 ≤ plusWeights0347 i) ∧
    (∀ i, 0 ≤ minusWeights0347 i) ∧
    (∀ i, plusCoefficients coefficients0347 upper0347 i = powerCoefficients10 plusWeights0347 i) ∧
    (∀ i, minusCoefficients coefficients0347 upper0347 i = powerCoefficients10 minusWeights0347 i) := by
  decide +kernel

theorem bound0347 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0347 g| ≤ (upper0347 : ℝ) :=
  abs_of_coefficients coefficients0347 upper0347 powerCoefficients10 plusWeights0347 minusWeights0347
    checked0347.1 checked0347.2.1 checked0347.2.2.1 checked0347.2.2.2
    (power_identity10 plusWeights0347) (power_identity10 minusWeights0347) g hg hmax

def envelope0347 : Envelope := ⟨coefficients0347, upper0347, bound0347⟩

def coefficients0348 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/8192), (75/16384), (2625/131072)]

def upper0348 : ℚ := (1029/10485760000000)

def plusWeights0348 : Fin 11 → ℚ := ![(1029/10485760000000), (1029/1048576000000), (9261/2097152000000), (3087/262144000000), (21609/1048576000000), (64827/2621440000000), (21609/1048576000000), (3087/262144000000), (9453/2097152000000), (6129/5242880000000), (1029/5242880000000)]

def minusWeights0348 : Fin 11 → ℚ := ![(1029/10485760000000), (1029/1048576000000), (9261/2097152000000), (3087/262144000000), (21609/1048576000000), (64827/2621440000000), (21609/1048576000000), (3087/262144000000), (9069/2097152000000), (4161/5242880000000), 0]

theorem checked0348 :
    (∀ i, 0 ≤ plusWeights0348 i) ∧
    (∀ i, 0 ≤ minusWeights0348 i) ∧
    (∀ i, plusCoefficients coefficients0348 upper0348 i = powerCoefficients10 plusWeights0348 i) ∧
    (∀ i, minusCoefficients coefficients0348 upper0348 i = powerCoefficients10 minusWeights0348 i) := by
  decide +kernel

theorem bound0348 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0348 g| ≤ (upper0348 : ℝ) :=
  abs_of_coefficients coefficients0348 upper0348 powerCoefficients10 plusWeights0348 minusWeights0348
    checked0348.1 checked0348.2.1 checked0348.2.2.1 checked0348.2.2.2
    (power_identity10 plusWeights0348) (power_identity10 minusWeights0348) g hg hmax

def envelope0348 : Envelope := ⟨coefficients0348, upper0348, bound0348⟩

def coefficients0349 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (5/512), (5/512), (5/2048)]

def upper0349 : ℚ := (441/4096000000000)

def plusWeights0349 : Fin 11 → ℚ := ![(441/4096000000000), (441/409600000000), (3969/819200000000), (1323/102400000000), (9261/409600000000), (27783/1024000000000), (9261/409600000000), (1323/102400000000), (4049/819200000000), (21/16384000000), (441/2048000000000)]

def minusWeights0349 : Fin 11 → ℚ := ![(441/4096000000000), (441/409600000000), (3969/819200000000), (1323/102400000000), (9261/409600000000), (27783/1024000000000), (9261/409600000000), (1323/102400000000), (3889/819200000000), (357/409600000000), 0]

theorem checked0349 :
    (∀ i, 0 ≤ plusWeights0349 i) ∧
    (∀ i, 0 ≤ minusWeights0349 i) ∧
    (∀ i, plusCoefficients coefficients0349 upper0349 i = powerCoefficients10 plusWeights0349 i) ∧
    (∀ i, minusCoefficients coefficients0349 upper0349 i = powerCoefficients10 minusWeights0349 i) := by
  decide +kernel

theorem bound0349 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0349 g| ≤ (upper0349 : ℝ) :=
  abs_of_coefficients coefficients0349 upper0349 powerCoefficients10 plusWeights0349 minusWeights0349
    checked0349.1 checked0349.2.1 checked0349.2.2.1 checked0349.2.2.2
    (power_identity10 plusWeights0349) (power_identity10 minusWeights0349) g hg hmax

def envelope0349 : Envelope := ⟨coefficients0349, upper0349, bound0349⟩

def coefficients0350 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (45/4096), (45/4096), (45/16384)]

def upper0350 : ℚ := (3969/32768000000000)

def plusWeights0350 : Fin 11 → ℚ := ![(3969/32768000000000), (3969/3276800000000), (35721/6553600000000), (11907/819200000000), (83349/3276800000000), (250047/8192000000000), (83349/3276800000000), (11907/819200000000), (36441/6553600000000), (189/131072000000), (3969/16384000000000)]

def minusWeights0350 : Fin 11 → ℚ := ![(3969/32768000000000), (3969/3276800000000), (35721/6553600000000), (11907/819200000000), (83349/3276800000000), (250047/8192000000000), (83349/3276800000000), (11907/819200000000), (35001/6553600000000), (3213/3276800000000), 0]

theorem checked0350 :
    (∀ i, 0 ≤ plusWeights0350 i) ∧
    (∀ i, 0 ≤ minusWeights0350 i) ∧
    (∀ i, plusCoefficients coefficients0350 upper0350 i = powerCoefficients10 plusWeights0350 i) ∧
    (∀ i, minusCoefficients coefficients0350 upper0350 i = powerCoefficients10 minusWeights0350 i) := by
  decide +kernel

theorem bound0350 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0350 g| ≤ (upper0350 : ℝ) :=
  abs_of_coefficients coefficients0350 upper0350 powerCoefficients10 plusWeights0350 minusWeights0350
    checked0350.1 checked0350.2.1 checked0350.2.2.1 checked0350.2.2.2
    (power_identity10 plusWeights0350) (power_identity10 minusWeights0350) g hg hmax

def envelope0350 : Envelope := ⟨coefficients0350, upper0350, bound0350⟩

def coefficients0351 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/32768), (585/65536), (1215/65536)]

def upper0351 : ℚ := (17613/131072000000000)

def plusWeights0351 : Fin 11 → ℚ := ![(17613/131072000000000), (17613/13107200000000), (158517/26214400000000), (52839/3276800000000), (369873/13107200000000), (1109619/32768000000000), (369873/13107200000000), (52839/3276800000000), (161757/26214400000000), (2097/1310720000000), (17613/65536000000000)]

def minusWeights0351 : Fin 11 → ℚ := ![(17613/131072000000000), (17613/13107200000000), (158517/26214400000000), (52839/3276800000000), (369873/13107200000000), (1109619/32768000000000), (369873/13107200000000), (52839/3276800000000), (155277/26214400000000), (891/819200000000), 0]

theorem checked0351 :
    (∀ i, 0 ≤ plusWeights0351 i) ∧
    (∀ i, 0 ≤ minusWeights0351 i) ∧
    (∀ i, plusCoefficients coefficients0351 upper0351 i = powerCoefficients10 plusWeights0351 i) ∧
    (∀ i, minusCoefficients coefficients0351 upper0351 i = powerCoefficients10 minusWeights0351 i) := by
  decide +kernel

theorem bound0351 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0351 g| ≤ (upper0351 : ℝ) :=
  abs_of_coefficients coefficients0351 upper0351 powerCoefficients10 plusWeights0351 minusWeights0351
    checked0351.1 checked0351.2.1 checked0351.2.2.1 checked0351.2.2.2
    (power_identity10 plusWeights0351) (power_identity10 minusWeights0351) g hg hmax

def envelope0351 : Envelope := ⟨coefficients0351, upper0351, bound0351⟩

end BilayerDressed.CubicQuarticEnvelopes

import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0384 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/4096), (585/8192), (3735/32768)]

def upper0384 : ℚ := (70227/65536000000000)

def plusWeights0384 : Fin 11 → ℚ := ![(70227/65536000000000), (70227/6553600000000), (632043/13107200000000), (210681/1638400000000), (1474767/6553600000000), (4424301/16384000000000), (1474767/6553600000000), (210681/1638400000000), (645003/13107200000000), (16731/1310720000000), (70227/32768000000000)]

def minusWeights0384 : Fin 11 → ℚ := ![(70227/65536000000000), (70227/6553600000000), (632043/13107200000000), (210681/1638400000000), (1474767/6553600000000), (4424301/16384000000000), (1474767/6553600000000), (210681/1638400000000), (619083/13107200000000), (56799/6553600000000), 0]

theorem checked0384 :
    (∀ i, 0 ≤ plusWeights0384 i) ∧
    (∀ i, 0 ≤ minusWeights0384 i) ∧
    (∀ i, plusCoefficients coefficients0384 upper0384 i = powerCoefficients10 plusWeights0384 i) ∧
    (∀ i, minusCoefficients coefficients0384 upper0384 i = powerCoefficients10 minusWeights0384 i) := by
  decide +kernel

theorem bound0384 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0384 g| ≤ (upper0384 : ℝ) :=
  abs_of_coefficients coefficients0384 upper0384 powerCoefficients10 plusWeights0384 minusWeights0384
    checked0384.1 checked0384.2.1 checked0384.2.2.1 checked0384.2.2.2
    (power_identity10 plusWeights0384) (power_identity10 minusWeights0384) g hg hmax

def envelope0384 : Envelope := ⟨coefficients0384, upper0384, bound0384⟩

def coefficients0385 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/4096), (585/8192), (1215/8192)]

def upper0385 : ℚ := (17613/16384000000000)

def plusWeights0385 : Fin 11 → ℚ := ![(17613/16384000000000), (17613/1638400000000), (158517/3276800000000), (52839/409600000000), (369873/1638400000000), (1109619/4096000000000), (369873/1638400000000), (52839/409600000000), (161757/3276800000000), (2097/163840000000), (17613/8192000000000)]

def minusWeights0385 : Fin 11 → ℚ := ![(17613/16384000000000), (17613/1638400000000), (158517/3276800000000), (52839/409600000000), (369873/1638400000000), (1109619/4096000000000), (369873/1638400000000), (52839/409600000000), (155277/3276800000000), (891/102400000000), 0]

theorem checked0385 :
    (∀ i, 0 ≤ plusWeights0385 i) ∧
    (∀ i, 0 ≤ minusWeights0385 i) ∧
    (∀ i, plusCoefficients coefficients0385 upper0385 i = powerCoefficients10 plusWeights0385 i) ∧
    (∀ i, minusCoefficients coefficients0385 upper0385 i = powerCoefficients10 minusWeights0385 i) := by
  decide +kernel

theorem bound0385 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0385 g| ≤ (upper0385 : ℝ) :=
  abs_of_coefficients coefficients0385 upper0385 powerCoefficients10 plusWeights0385 minusWeights0385
    checked0385.1 checked0385.2.1 checked0385.2.2.1 checked0385.2.2.2
    (power_identity10 plusWeights0385) (power_identity10 minusWeights0385) g hg hmax

def envelope0385 : Envelope := ⟨coefficients0385, upper0385, bound0385⟩

def coefficients0386 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (105/1024), (105/1024), (105/4096)]

def upper0386 : ℚ := (9261/8192000000000)

def plusWeights0386 : Fin 11 → ℚ := ![(9261/8192000000000), (9261/819200000000), (83349/1638400000000), (27783/204800000000), (194481/819200000000), (583443/2048000000000), (194481/819200000000), (27783/204800000000), (85029/1638400000000), (441/32768000000), (9261/4096000000000)]

def minusWeights0386 : Fin 11 → ℚ := ![(9261/8192000000000), (9261/819200000000), (83349/1638400000000), (27783/204800000000), (194481/819200000000), (583443/2048000000000), (194481/819200000000), (27783/204800000000), (81669/1638400000000), (7497/819200000000), 0]

theorem checked0386 :
    (∀ i, 0 ≤ plusWeights0386 i) ∧
    (∀ i, 0 ≤ minusWeights0386 i) ∧
    (∀ i, plusCoefficients coefficients0386 upper0386 i = powerCoefficients10 plusWeights0386 i) ∧
    (∀ i, minusCoefficients coefficients0386 upper0386 i = powerCoefficients10 minusWeights0386 i) := by
  decide +kernel

theorem bound0386 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0386 g| ≤ (upper0386 : ℝ) :=
  abs_of_coefficients coefficients0386 upper0386 powerCoefficients10 plusWeights0386 minusWeights0386
    checked0386.1 checked0386.2.1 checked0386.2.2.1 checked0386.2.2.2
    (power_identity10 plusWeights0386) (power_identity10 minusWeights0386) g hg hmax

def envelope0386 : Envelope := ⟨coefficients0386, upper0386, bound0386⟩

def coefficients0387 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (225/2048), (225/4096), (1125/32768)]

def upper0387 : ℚ := (3033/2621440000000)

def plusWeights0387 : Fin 11 → ℚ := ![(3033/2621440000000), (3033/262144000000), (27297/524288000000), (9099/65536000000), (63693/262144000000), (191079/655360000000), (63693/262144000000), (9099/65536000000), (27873/524288000000), (18117/1310720000000), (3033/1310720000000)]

def minusWeights0387 : Fin 11 → ℚ := ![(3033/2621440000000), (3033/262144000000), (27297/524288000000), (9099/65536000000), (63693/262144000000), (191079/655360000000), (63693/262144000000), (9099/65536000000), (26721/524288000000), (12213/1310720000000), 0]

theorem checked0387 :
    (∀ i, 0 ≤ plusWeights0387 i) ∧
    (∀ i, 0 ≤ minusWeights0387 i) ∧
    (∀ i, plusCoefficients coefficients0387 upper0387 i = powerCoefficients10 plusWeights0387 i) ∧
    (∀ i, minusCoefficients coefficients0387 upper0387 i = powerCoefficients10 minusWeights0387 i) := by
  decide +kernel

theorem bound0387 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0387 g| ≤ (upper0387 : ℝ) :=
  abs_of_coefficients coefficients0387 upper0387 powerCoefficients10 plusWeights0387 minusWeights0387
    checked0387.1 checked0387.2.1 checked0387.2.2.1 checked0387.2.2.2
    (power_identity10 plusWeights0387) (power_identity10 minusWeights0387) g hg hmax

def envelope0387 : Envelope := ⟨coefficients0387, upper0387, bound0387⟩

def coefficients0388 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (945/8192), (1365/16384), (8715/65536)]

def upper0388 : ℚ := (163863/131072000000000)

def plusWeights0388 : Fin 11 → ℚ := ![(163863/131072000000000), (163863/13107200000000), (1474767/26214400000000), (491589/3276800000000), (3441123/13107200000000), (10323369/32768000000000), (3441123/13107200000000), (491589/3276800000000), (1505007/26214400000000), (39039/2621440000000), (163863/65536000000000)]

def minusWeights0388 : Fin 11 → ℚ := ![(163863/131072000000000), (163863/13107200000000), (1474767/26214400000000), (491589/3276800000000), (3441123/13107200000000), (10323369/32768000000000), (3441123/13107200000000), (491589/3276800000000), (1444527/26214400000000), (132531/13107200000000), 0]

theorem checked0388 :
    (∀ i, 0 ≤ plusWeights0388 i) ∧
    (∀ i, 0 ≤ minusWeights0388 i) ∧
    (∀ i, plusCoefficients coefficients0388 upper0388 i = powerCoefficients10 plusWeights0388 i) ∧
    (∀ i, minusCoefficients coefficients0388 upper0388 i = powerCoefficients10 minusWeights0388 i) := by
  decide +kernel

theorem bound0388 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0388 g| ≤ (upper0388 : ℝ) :=
  abs_of_coefficients coefficients0388 upper0388 powerCoefficients10 plusWeights0388 minusWeights0388
    checked0388.1 checked0388.2.1 checked0388.2.2.1 checked0388.2.2.2
    (power_identity10 plusWeights0388) (power_identity10 minusWeights0388) g hg hmax

def envelope0388 : Envelope := ⟨coefficients0388, upper0388, bound0388⟩

def coefficients0389 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (5/8192), (5/512), (-115/65536), (-275/131072)]

def upper0389 : ℚ := (8423/52428800000000)

def plusWeights0389 : Fin 11 → ℚ := ![(8423/52428800000000), (8423/5242880000000), (75807/10485760000000), (25269/1310720000000), (176883/5242880000000), (530649/13107200000000), (176883/5242880000000), (25349/1310720000000), (78751/10485760000000), (51989/26214400000000), (13/40960000000)]

def minusWeights0389 : Fin 11 → ℚ := ![(8423/52428800000000), (8423/5242880000000), (75807/10485760000000), (25269/1310720000000), (176883/5242880000000), (530649/13107200000000), (176883/5242880000000), (25189/1310720000000), (72863/10485760000000), (32241/26214400000000), (103/26214400000000)]

theorem checked0389 :
    (∀ i, 0 ≤ plusWeights0389 i) ∧
    (∀ i, 0 ≤ minusWeights0389 i) ∧
    (∀ i, plusCoefficients coefficients0389 upper0389 i = powerCoefficients10 plusWeights0389 i) ∧
    (∀ i, minusCoefficients coefficients0389 upper0389 i = powerCoefficients10 minusWeights0389 i) := by
  decide +kernel

theorem bound0389 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0389 g| ≤ (upper0389 : ℝ) :=
  abs_of_coefficients coefficients0389 upper0389 powerCoefficients10 plusWeights0389 minusWeights0389
    checked0389.1 checked0389.2.1 checked0389.2.2.1 checked0389.2.2.2
    (power_identity10 plusWeights0389) (power_identity10 minusWeights0389) g hg hmax

def envelope0389 : Envelope := ⟨coefficients0389, upper0389, bound0389⟩

def coefficients0390 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/256), (-7/8192), (19/8192), (49/8192), (55/32768)]

def upper0390 : ℚ := (252323/65536000000000)

def plusWeights0390 : Fin 11 → ℚ := ![(252323/65536000000000), (252323/6553600000000), (2270907/13107200000000), (756969/1638400000000), (5298783/6553600000000), (15896349/16384000000000), (5324383/6553600000000), (782429/1638400000000), (2575051/13107200000000), (1766931/32768000000000), (252323/32768000000000)]

def minusWeights0390 : Fin 11 → ℚ := ![(252323/65536000000000), (252323/6553600000000), (2270907/13107200000000), (756969/1638400000000), (5298783/6553600000000), (15896349/16384000000000), (5273183/6553600000000), (731509/1638400000000), (1966763/13107200000000), (756299/32768000000000), 0]

theorem checked0390 :
    (∀ i, 0 ≤ plusWeights0390 i) ∧
    (∀ i, 0 ≤ minusWeights0390 i) ∧
    (∀ i, plusCoefficients coefficients0390 upper0390 i = powerCoefficients10 plusWeights0390 i) ∧
    (∀ i, minusCoefficients coefficients0390 upper0390 i = powerCoefficients10 minusWeights0390 i) := by
  decide +kernel

theorem bound0390 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0390 g| ≤ (upper0390 : ℝ) :=
  abs_of_coefficients coefficients0390 upper0390 powerCoefficients10 plusWeights0390 minusWeights0390
    checked0390.1 checked0390.2.1 checked0390.2.2.1 checked0390.2.2.2
    (power_identity10 plusWeights0390) (power_identity10 minusWeights0390) g hg hmax

def envelope0390 : Envelope := ⟨coefficients0390, upper0390, bound0390⟩

def coefficients0391 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/2048), (-31/8192), (359/16384), (383/32768), (4075/262144)]

def upper0391 : ℚ := (2227423/524288000000000)

def plusWeights0391 : Fin 11 → ℚ := ![(2227423/524288000000000), (2227423/52428800000000), (20046807/104857600000000), (6682269/13107200000000), (46775883/52428800000000), (140327649/131072000000000), (47006283/52428800000000), (6907709/13107200000000), (22715543/104857600000000), (15565459/262144000000000), (2227423/262144000000000)]

def minusWeights0391 : Fin 11 → ℚ := ![(2227423/524288000000000), (2227423/52428800000000), (20046807/104857600000000), (6682269/13107200000000), (46775883/52428800000000), (140327649/131072000000000), (46545483/52428800000000), (6456829/13107200000000), (17378071/104857600000000), (6708771/262144000000000), 0]

theorem checked0391 :
    (∀ i, 0 ≤ plusWeights0391 i) ∧
    (∀ i, 0 ≤ minusWeights0391 i) ∧
    (∀ i, plusCoefficients coefficients0391 upper0391 i = powerCoefficients10 plusWeights0391 i) ∧
    (∀ i, minusCoefficients coefficients0391 upper0391 i = powerCoefficients10 minusWeights0391 i) := by
  decide +kernel

theorem bound0391 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0391 g| ≤ (upper0391 : ℝ) :=
  abs_of_coefficients coefficients0391 upper0391 powerCoefficients10 plusWeights0391 minusWeights0391
    checked0391.1 checked0391.2.1 checked0391.2.2.1 checked0391.2.2.2
    (power_identity10 plusWeights0391) (power_identity10 minusWeights0391) g hg hmax

def envelope0391 : Envelope := ⟨coefficients0391, upper0391, bound0391⟩

def coefficients0392 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/1024), (-89/4096), (-111/4096), (-1219/32768), (-973/65536)]

def upper0392 : ℚ := (1573047/655360000000000)

def plusWeights0392 : Fin 11 → ℚ := ![(1573047/655360000000000), (1573047/65536000000000), (14157423/131072000000000), (4719141/16384000000000), (33033987/65536000000000), (99101961/163840000000000), (33353987/65536000000000), (5003541/16384000000000), (17107503/131072000000000), (2387889/65536000000000), (1573047/327680000000000)]

def minusWeights0392 : Fin 11 → ℚ := ![(1573047/655360000000000), (1573047/65536000000000), (14157423/131072000000000), (4719141/16384000000000), (33033987/65536000000000), (99101961/163840000000000), (32713987/65536000000000), (4434741/16384000000000), (11207343/131072000000000), (151641/13107200000000), 0]

theorem checked0392 :
    (∀ i, 0 ≤ plusWeights0392 i) ∧
    (∀ i, 0 ≤ minusWeights0392 i) ∧
    (∀ i, plusCoefficients coefficients0392 upper0392 i = powerCoefficients10 plusWeights0392 i) ∧
    (∀ i, minusCoefficients coefficients0392 upper0392 i = powerCoefficients10 minusWeights0392 i) := by
  decide +kernel

theorem bound0392 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0392 g| ≤ (upper0392 : ℝ) :=
  abs_of_coefficients coefficients0392 upper0392 powerCoefficients10 plusWeights0392 minusWeights0392
    checked0392.1 checked0392.2.1 checked0392.2.2.1 checked0392.2.2.2
    (power_identity10 plusWeights0392) (power_identity10 minusWeights0392) g hg hmax

def envelope0392 : Envelope := ⟨coefficients0392, upper0392, bound0392⟩

def coefficients0393 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/1024), (-35/4096), (-45/4096), (-315/32768), (-225/65536)]

def upper0393 : ℚ := (102459/26214400000000)

def plusWeights0393 : Fin 11 → ℚ := ![(102459/26214400000000), (102459/2621440000000), (922131/5242880000000), (307377/655360000000), (2151639/2621440000000), (6454917/6553600000000), (2164439/2621440000000), (319617/655360000000), (212343/1048576000000), (731689/13107200000000), (102459/13107200000000)]

def minusWeights0393 : Fin 11 → ℚ := ![(102459/26214400000000), (102459/2621440000000), (922131/5242880000000), (307377/655360000000), (2151639/2621440000000), (6454917/6553600000000), (2138839/2621440000000), (295137/655360000000), (782547/5242880000000), (292901/13107200000000), 0]

theorem checked0393 :
    (∀ i, 0 ≤ plusWeights0393 i) ∧
    (∀ i, 0 ≤ minusWeights0393 i) ∧
    (∀ i, plusCoefficients coefficients0393 upper0393 i = powerCoefficients10 plusWeights0393 i) ∧
    (∀ i, minusCoefficients coefficients0393 upper0393 i = powerCoefficients10 minusWeights0393 i) := by
  decide +kernel

theorem bound0393 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0393 g| ≤ (upper0393 : ℝ) :=
  abs_of_coefficients coefficients0393 upper0393 powerCoefficients10 plusWeights0393 minusWeights0393
    checked0393.1 checked0393.2.1 checked0393.2.2.1 checked0393.2.2.2
    (power_identity10 plusWeights0393) (power_identity10 minusWeights0393) g hg hmax

def envelope0393 : Envelope := ⟨coefficients0393, upper0393, bound0393⟩

def coefficients0394 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/1024), (-7/2048), (-13/2048), (-453/65536), (-341/131072)]

def upper0394 : ℚ := (5859399/1310720000000000)

def plusWeights0394 : Fin 11 → ℚ := ![(5859399/1310720000000000), (5859399/131072000000000), (52734591/262144000000000), (17578197/32768000000000), (123047379/131072000000000), (369142137/327680000000000), (123687379/131072000000000), (18206997/32768000000000), (60129151/262144000000000), (8267453/131072000000000), (5859399/655360000000000)]

def minusWeights0394 : Fin 11 → ℚ := ![(5859399/1310720000000000), (5859399/131072000000000), (52734591/262144000000000), (17578197/32768000000000), (123047379/131072000000000), (369142137/327680000000000), (122407379/131072000000000), (16949397/32768000000000), (45340031/262144000000000), (690269/26214400000000), 0]

theorem checked0394 :
    (∀ i, 0 ≤ plusWeights0394 i) ∧
    (∀ i, 0 ≤ minusWeights0394 i) ∧
    (∀ i, plusCoefficients coefficients0394 upper0394 i = powerCoefficients10 plusWeights0394 i) ∧
    (∀ i, minusCoefficients coefficients0394 upper0394 i = powerCoefficients10 minusWeights0394 i) := by
  decide +kernel

theorem bound0394 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0394 g| ≤ (upper0394 : ℝ) :=
  abs_of_coefficients coefficients0394 upper0394 powerCoefficients10 plusWeights0394 minusWeights0394
    checked0394.1 checked0394.2.1 checked0394.2.2.1 checked0394.2.2.2
    (power_identity10 plusWeights0394) (power_identity10 minusWeights0394) g hg hmax

def envelope0394 : Envelope := ⟨coefficients0394, upper0394, bound0394⟩

def coefficients0395 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/1024), (5/1024), (15/2048), (25/8192), (125/65536)]

def upper0395 : ℚ := (28561/5242880000000)

def plusWeights0395 : Fin 11 → ℚ := ![(28561/5242880000000), (28561/524288000000), (257049/1048576000000), (85683/131072000000), (599781/524288000000), (1799343/1310720000000), (602341/524288000000), (88307/131072000000), (1446909/5242880000000), (198237/2621440000000), (28561/2621440000000)]

def minusWeights0395 : Fin 11 → ℚ := ![(28561/5242880000000), (28561/524288000000), (257049/1048576000000), (85683/131072000000), (599781/524288000000), (1799343/1310720000000), (597221/524288000000), (83059/131072000000), (1123581/5242880000000), (87373/2621440000000), 0]

theorem checked0395 :
    (∀ i, 0 ≤ plusWeights0395 i) ∧
    (∀ i, 0 ≤ minusWeights0395 i) ∧
    (∀ i, plusCoefficients coefficients0395 upper0395 i = powerCoefficients10 plusWeights0395 i) ∧
    (∀ i, minusCoefficients coefficients0395 upper0395 i = powerCoefficients10 minusWeights0395 i) := by
  decide +kernel

theorem bound0395 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0395 g| ≤ (upper0395 : ℝ) :=
  abs_of_coefficients coefficients0395 upper0395 powerCoefficients10 plusWeights0395 minusWeights0395
    checked0395.1 checked0395.2.1 checked0395.2.2.1 checked0395.2.2.2
    (power_identity10 plusWeights0395) (power_identity10 minusWeights0395) g hg hmax

def envelope0395 : Envelope := ⟨coefficients0395, upper0395, bound0395⟩

def coefficients0396 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/1024), (119/8192), (41/4096), (9/1024), (35/16384)]

def upper0396 : ℚ := (11007/1310720000000)

def plusWeights0396 : Fin 11 → ℚ := ![(11007/1310720000000), (11007/131072000000), (99063/262144000000), (33021/32768000000), (231147/131072000000), (693441/327680000000), (232043/131072000000), (169823/163840000000), (2774591/6553600000000), (1898699/16384000000000), (11007/655360000000)]

def minusWeights0396 : Fin 11 → ℚ := ![(11007/1310720000000), (11007/131072000000), (99063/262144000000), (33021/32768000000), (231147/131072000000), (693441/327680000000), (230251/131072000000), (160387/163840000000), (2178559/6553600000000), (853051/16384000000000), 0]

theorem checked0396 :
    (∀ i, 0 ≤ plusWeights0396 i) ∧
    (∀ i, 0 ≤ minusWeights0396 i) ∧
    (∀ i, plusCoefficients coefficients0396 upper0396 i = powerCoefficients10 plusWeights0396 i) ∧
    (∀ i, minusCoefficients coefficients0396 upper0396 i = powerCoefficients10 minusWeights0396 i) := by
  decide +kernel

theorem bound0396 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0396 g| ≤ (upper0396 : ℝ) :=
  abs_of_coefficients coefficients0396 upper0396 powerCoefficients10 plusWeights0396 minusWeights0396
    checked0396.1 checked0396.2.1 checked0396.2.2.1 checked0396.2.2.2
    (power_identity10 plusWeights0396) (power_identity10 minusWeights0396) g hg hmax

def envelope0396 : Envelope := ⟨coefficients0396, upper0396, bound0396⟩

def coefficients0397 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/2048), (5/2048), (305/32768), (525/65536), (775/262144)]

def upper0397 : ℚ := (804231/104857600000000)

def plusWeights0397 : Fin 11 → ℚ := ![(804231/104857600000000), (804231/10485760000000), (7238079/20971520000000), (2412693/2621440000000), (16888851/10485760000000), (50666553/26214400000000), (16965651/10485760000000), (2490133/2621440000000), (8176991/20971520000000), (1121147/10485760000000), (804231/52428800000000)]

def minusWeights0397 : Fin 11 → ℚ := ![(804231/104857600000000), (804231/10485760000000), (7238079/20971520000000), (2412693/2621440000000), (16888851/10485760000000), (50666553/26214400000000), (16812051/10485760000000), (2335253/2621440000000), (6299167/20971520000000), (97463/2097152000000), 0]

theorem checked0397 :
    (∀ i, 0 ≤ plusWeights0397 i) ∧
    (∀ i, 0 ≤ minusWeights0397 i) ∧
    (∀ i, plusCoefficients coefficients0397 upper0397 i = powerCoefficients10 plusWeights0397 i) ∧
    (∀ i, minusCoefficients coefficients0397 upper0397 i = powerCoefficients10 minusWeights0397 i) := by
  decide +kernel

theorem bound0397 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0397 g| ≤ (upper0397 : ℝ) :=
  abs_of_coefficients coefficients0397 upper0397 powerCoefficients10 plusWeights0397 minusWeights0397
    checked0397.1 checked0397.2.1 checked0397.2.2.1 checked0397.2.2.2
    (power_identity10 plusWeights0397) (power_identity10 minusWeights0397) g hg hmax

def envelope0397 : Envelope := ⟨coefficients0397, upper0397, bound0397⟩

def coefficients0398 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/2048), (5/1024), (225/16384), (305/32768), (2735/262144)]

def upper0398 : ℚ := (4173427/524288000000000)

def plusWeights0398 : Fin 11 → ℚ := ![(4173427/524288000000000), (4173427/52428800000000), (37560843/104857600000000), (12520281/13107200000000), (87641967/52428800000000), (262925901/131072000000000), (88025967/52428800000000), (12910681/13107200000000), (42336843/104857600000000), (1160223/10485760000000), (4173427/262144000000000)]

def minusWeights0398 : Fin 11 → ℚ := ![(4173427/524288000000000), (4173427/52428800000000), (37560843/104857600000000), (12520281/13107200000000), (87641967/52428800000000), (262925901/131072000000000), (87257967/52428800000000), (12129881/13107200000000), (32784843/104857600000000), (2545739/52428800000000), 0]

theorem checked0398 :
    (∀ i, 0 ≤ plusWeights0398 i) ∧
    (∀ i, 0 ≤ minusWeights0398 i) ∧
    (∀ i, plusCoefficients coefficients0398 upper0398 i = powerCoefficients10 plusWeights0398 i) ∧
    (∀ i, minusCoefficients coefficients0398 upper0398 i = powerCoefficients10 minusWeights0398 i) := by
  decide +kernel

theorem bound0398 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0398 g| ≤ (upper0398 : ℝ) :=
  abs_of_coefficients coefficients0398 upper0398 powerCoefficients10 plusWeights0398 minusWeights0398
    checked0398.1 checked0398.2.1 checked0398.2.2.1 checked0398.2.2.2
    (power_identity10 plusWeights0398) (power_identity10 minusWeights0398) g hg hmax

def envelope0398 : Envelope := ⟨coefficients0398, upper0398, bound0398⟩

def coefficients0399 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/128), (3/256), (13/512), (21/1024), (5/1024)]

def upper0399 : ℚ := (18963/2048000000000)

def plusWeights0399 : Fin 11 → ℚ := ![(18963/2048000000000), (18963/204800000000), (170667/409600000000), (56889/51200000000), (398223/204800000000), (1194669/512000000000), (399823/204800000000), (58549/51200000000), (191411/409600000000), (32739/256000000000), (18963/1024000000000)]

def minusWeights0399 : Fin 11 → ℚ := ![(18963/2048000000000), (18963/204800000000), (170667/409600000000), (56889/51200000000), (398223/204800000000), (1194669/512000000000), (396623/204800000000), (55229/51200000000), (149923/409600000000), (29337/512000000000), 0]

theorem checked0399 :
    (∀ i, 0 ≤ plusWeights0399 i) ∧
    (∀ i, 0 ≤ minusWeights0399 i) ∧
    (∀ i, plusCoefficients coefficients0399 upper0399 i = powerCoefficients10 plusWeights0399 i) ∧
    (∀ i, minusCoefficients coefficients0399 upper0399 i = powerCoefficients10 minusWeights0399 i) := by
  decide +kernel

theorem bound0399 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0399 g| ≤ (upper0399 : ℝ) :=
  abs_of_coefficients coefficients0399 upper0399 powerCoefficients10 plusWeights0399 minusWeights0399
    checked0399.1 checked0399.2.1 checked0399.2.2.1 checked0399.2.2.2
    (power_identity10 plusWeights0399) (power_identity10 minusWeights0399) g hg hmax

def envelope0399 : Envelope := ⟨coefficients0399, upper0399, bound0399⟩

def coefficients0400 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/128), (3/256), (9/256), (31/1024), (15/2048)]

def upper0400 : ℚ := (38367/4096000000000)

def plusWeights0400 : Fin 11 → ℚ := ![(38367/4096000000000), (38367/409600000000), (345303/819200000000), (115101/102400000000), (805707/409600000000), (2417121/1024000000000), (808907/409600000000), (118421/102400000000), (386871/819200000000), (264537/2048000000000), (38367/2048000000000)]

def minusWeights0400 : Fin 11 → ℚ := ![(38367/4096000000000), (38367/409600000000), (345303/819200000000), (115101/102400000000), (805707/409600000000), (2417121/1024000000000), (802507/409600000000), (111781/102400000000), (60747/163840000000), (119133/2048000000000), 0]

theorem checked0400 :
    (∀ i, 0 ≤ plusWeights0400 i) ∧
    (∀ i, 0 ≤ minusWeights0400 i) ∧
    (∀ i, plusCoefficients coefficients0400 upper0400 i = powerCoefficients10 plusWeights0400 i) ∧
    (∀ i, minusCoefficients coefficients0400 upper0400 i = powerCoefficients10 minusWeights0400 i) := by
  decide +kernel

theorem bound0400 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0400 g| ≤ (upper0400 : ℝ) :=
  abs_of_coefficients coefficients0400 upper0400 powerCoefficients10 plusWeights0400 minusWeights0400
    checked0400.1 checked0400.2.1 checked0400.2.2.1 checked0400.2.2.2
    (power_identity10 plusWeights0400) (power_identity10 minusWeights0400) g hg hmax

def envelope0400 : Envelope := ⟨coefficients0400, upper0400, bound0400⟩

def coefficients0401 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/1024), (-31/4096), (97/4096), (89/8192), (1455/262144)]

def upper0401 : ℚ := (4341347/524288000000000)

def plusWeights0401 : Fin 11 → ℚ := ![(4341347/524288000000000), (4341347/52428800000000), (39072123/104857600000000), (13024041/13107200000000), (91168287/52428800000000), (273504861/131072000000000), (91629087/52428800000000), (13474921/13107200000000), (1775539/4194304000000), (30454543/262144000000000), (4341347/262144000000000)]

def minusWeights0401 : Fin 11 → ℚ := ![(4341347/524288000000000), (4341347/52428800000000), (39072123/104857600000000), (13024041/13107200000000), (91168287/52428800000000), (273504861/131072000000000), (90707487/52428800000000), (12573161/13107200000000), (33755771/104857600000000), (12958927/262144000000000), 0]

theorem checked0401 :
    (∀ i, 0 ≤ plusWeights0401 i) ∧
    (∀ i, 0 ≤ minusWeights0401 i) ∧
    (∀ i, plusCoefficients coefficients0401 upper0401 i = powerCoefficients10 plusWeights0401 i) ∧
    (∀ i, minusCoefficients coefficients0401 upper0401 i = powerCoefficients10 minusWeights0401 i) := by
  decide +kernel

theorem bound0401 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0401 g| ≤ (upper0401 : ℝ) :=
  abs_of_coefficients coefficients0401 upper0401 powerCoefficients10 plusWeights0401 minusWeights0401
    checked0401.1 checked0401.2.1 checked0401.2.2.1 checked0401.2.2.2
    (power_identity10 plusWeights0401) (power_identity10 minusWeights0401) g hg hmax

def envelope0401 : Envelope := ⟨coefficients0401, upper0401, bound0401⟩

def coefficients0402 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/1024), (-31/4096), (533/16384), (521/32768), (1955/131072)]

def upper0402 : ℚ := (2195439/262144000000000)

def plusWeights0402 : Fin 11 → ℚ := ![(2195439/262144000000000), (2195439/26214400000000), (19758951/52428800000000), (6586317/6553600000000), (46104219/26214400000000), (138312657/65536000000000), (46334619/26214400000000), (6811757/6553600000000), (22421767/52428800000000), (15374959/131072000000000), (2195439/131072000000000)]

def minusWeights0402 : Fin 11 → ℚ := ![(2195439/262144000000000), (2195439/26214400000000), (19758951/52428800000000), (6586317/6553600000000), (46104219/26214400000000), (138312657/65536000000000), (45873819/26214400000000), (6360877/6553600000000), (3419227/10485760000000), (6579431/131072000000000), 0]

theorem checked0402 :
    (∀ i, 0 ≤ plusWeights0402 i) ∧
    (∀ i, 0 ≤ minusWeights0402 i) ∧
    (∀ i, plusCoefficients coefficients0402 upper0402 i = powerCoefficients10 plusWeights0402 i) ∧
    (∀ i, minusCoefficients coefficients0402 upper0402 i = powerCoefficients10 minusWeights0402 i) := by
  decide +kernel

theorem bound0402 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0402 g| ≤ (upper0402 : ℝ) :=
  abs_of_coefficients coefficients0402 upper0402 powerCoefficients10 plusWeights0402 minusWeights0402
    checked0402.1 checked0402.2.1 checked0402.2.2.1 checked0402.2.2.2
    (power_identity10 plusWeights0402) (power_identity10 minusWeights0402) g hg hmax

def envelope0402 : Envelope := ⟨coefficients0402, upper0402, bound0402⟩

def coefficients0403 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/1024), (-31/4096), (1343/16384), (1691/32768), (1225/16384)]

def upper0403 : ℚ := (72999/8192000000000)

def plusWeights0403 : Fin 11 → ℚ := ![(72999/8192000000000), (72999/819200000000), (656991/1638400000000), (218997/204800000000), (1532979/819200000000), (4598937/2048000000000), (1540179/819200000000), (113021/102400000000), (370507/819200000000), (4052971/32768000000000), (72999/4096000000000)]

def minusWeights0403 : Fin 11 → ℚ := ![(72999/8192000000000), (72999/819200000000), (656991/1638400000000), (218997/204800000000), (1532979/819200000000), (4598937/2048000000000), (1525779/819200000000), (13247/12800000000), (71621/204800000000), (1786949/32768000000000), 0]

theorem checked0403 :
    (∀ i, 0 ≤ plusWeights0403 i) ∧
    (∀ i, 0 ≤ minusWeights0403 i) ∧
    (∀ i, plusCoefficients coefficients0403 upper0403 i = powerCoefficients10 plusWeights0403 i) ∧
    (∀ i, minusCoefficients coefficients0403 upper0403 i = powerCoefficients10 minusWeights0403 i) := by
  decide +kernel

theorem bound0403 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0403 g| ≤ (upper0403 : ℝ) :=
  abs_of_coefficients coefficients0403 upper0403 powerCoefficients10 plusWeights0403 minusWeights0403
    checked0403.1 checked0403.2.1 checked0403.2.2.1 checked0403.2.2.2
    (power_identity10 plusWeights0403) (power_identity10 minusWeights0403) g hg hmax

def envelope0403 : Envelope := ⟨coefficients0403, upper0403, bound0403⟩

def coefficients0404 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/1024), (13/8192), (1411/32768), (1707/65536), (17725/524288)]

def upper0404 : ℚ := (9864777/1048576000000000)

def plusWeights0404 : Fin 11 → ℚ := ![(9864777/1048576000000000), (9864777/104857600000000), (88782993/209715200000000), (29594331/26214400000000), (207160317/104857600000000), (621480951/262144000000000), (208081917/104857600000000), (30520091/26214400000000), (100032337/209715200000000), (68470661/524288000000000), (9864777/524288000000000)]

def minusWeights0404 : Fin 11 → ℚ := ![(9864777/1048576000000000), (9864777/104857600000000), (88782993/209715200000000), (29594331/26214400000000), (207160317/104857600000000), (621480951/262144000000000), (206238717/104857600000000), (28668571/26214400000000), (77533649/209715200000000), (30177109/524288000000000), 0]

theorem checked0404 :
    (∀ i, 0 ≤ plusWeights0404 i) ∧
    (∀ i, 0 ≤ minusWeights0404 i) ∧
    (∀ i, plusCoefficients coefficients0404 upper0404 i = powerCoefficients10 plusWeights0404 i) ∧
    (∀ i, minusCoefficients coefficients0404 upper0404 i = powerCoefficients10 minusWeights0404 i) := by
  decide +kernel

theorem bound0404 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0404 g| ≤ (upper0404 : ℝ) :=
  abs_of_coefficients coefficients0404 upper0404 powerCoefficients10 plusWeights0404 minusWeights0404
    checked0404.1 checked0404.2.1 checked0404.2.2.1 checked0404.2.2.2
    (power_identity10 plusWeights0404) (power_identity10 minusWeights0404) g hg hmax

def envelope0404 : Envelope := ⟨coefficients0404, upper0404, bound0404⟩

def coefficients0405 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/1024), (19/4096), (169/8192), (153/16384), (1205/262144)]

def upper0405 : ℚ := (4964497/524288000000000)

def plusWeights0405 : Fin 11 → ℚ := ![(4964497/524288000000000), (4964497/52428800000000), (44680473/104857600000000), (14893491/13107200000000), (104254437/52428800000000), (312763311/131072000000000), (104715237/52428800000000), (15360371/13107200000000), (403021/838860800000), (34513893/262144000000000), (4964497/262144000000000)]

def minusWeights0405 : Fin 11 → ℚ := ![(4964497/524288000000000), (4964497/52428800000000), (44680473/104857600000000), (14893491/13107200000000), (104254437/52428800000000), (312763311/131072000000000), (103793637/52428800000000), (14426611/13107200000000), (38983321/104857600000000), (15131077/262144000000000), 0]

theorem checked0405 :
    (∀ i, 0 ≤ plusWeights0405 i) ∧
    (∀ i, 0 ≤ minusWeights0405 i) ∧
    (∀ i, plusCoefficients coefficients0405 upper0405 i = powerCoefficients10 plusWeights0405 i) ∧
    (∀ i, minusCoefficients coefficients0405 upper0405 i = powerCoefficients10 minusWeights0405 i) := by
  decide +kernel

theorem bound0405 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0405 g| ≤ (upper0405 : ℝ) :=
  abs_of_coefficients coefficients0405 upper0405 powerCoefficients10 plusWeights0405 minusWeights0405
    checked0405.1 checked0405.2.1 checked0405.2.2.1 checked0405.2.2.2
    (power_identity10 plusWeights0405) (power_identity10 minusWeights0405) g hg hmax

def envelope0405 : Envelope := ⟨coefficients0405, upper0405, bound0405⟩

def coefficients0406 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/512), (-35/2048), (-45/2048), (-315/16384), (-225/32768)]

def upper0406 : ℚ := (102459/13107200000000)

def plusWeights0406 : Fin 11 → ℚ := ![(102459/13107200000000), (102459/1310720000000), (922131/2621440000000), (307377/327680000000), (2151639/1310720000000), (6454917/3276800000000), (2164439/1310720000000), (319617/327680000000), (212343/524288000000), (731689/6553600000000), (102459/6553600000000)]

def minusWeights0406 : Fin 11 → ℚ := ![(102459/13107200000000), (102459/1310720000000), (922131/2621440000000), (307377/327680000000), (2151639/1310720000000), (6454917/3276800000000), (2138839/1310720000000), (295137/327680000000), (782547/2621440000000), (292901/6553600000000), 0]

theorem checked0406 :
    (∀ i, 0 ≤ plusWeights0406 i) ∧
    (∀ i, 0 ≤ minusWeights0406 i) ∧
    (∀ i, plusCoefficients coefficients0406 upper0406 i = powerCoefficients10 plusWeights0406 i) ∧
    (∀ i, minusCoefficients coefficients0406 upper0406 i = powerCoefficients10 minusWeights0406 i) := by
  decide +kernel

theorem bound0406 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0406 g| ≤ (upper0406 : ℝ) :=
  abs_of_coefficients coefficients0406 upper0406 powerCoefficients10 plusWeights0406 minusWeights0406
    checked0406.1 checked0406.2.1 checked0406.2.2.1 checked0406.2.2.2
    (power_identity10 plusWeights0406) (power_identity10 minusWeights0406) g hg hmax

def envelope0406 : Envelope := ⟨coefficients0406, upper0406, bound0406⟩

def coefficients0407 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/512), (-25/2048), (-35/2048), (-315/32768), (-175/65536)]

def upper0407 : ℚ := (219261/26214400000000)

def plusWeights0407 : Fin 11 → ℚ := ![(219261/26214400000000), (219261/2621440000000), (1973349/5242880000000), (657783/655360000000), (4604481/2621440000000), (13813443/6553600000000), (4630081/2621440000000), (682583/655360000000), (2260453/5242880000000), (1555699/13107200000000), (219261/13107200000000)]

def minusWeights0407 : Fin 11 → ℚ := ![(219261/26214400000000), (219261/2621440000000), (1973349/5242880000000), (657783/655360000000), (4604481/2621440000000), (13813443/6553600000000), (4578881/2621440000000), (632983/655360000000), (337249/1048576000000), (636911/13107200000000), 0]

theorem checked0407 :
    (∀ i, 0 ≤ plusWeights0407 i) ∧
    (∀ i, 0 ≤ minusWeights0407 i) ∧
    (∀ i, plusCoefficients coefficients0407 upper0407 i = powerCoefficients10 plusWeights0407 i) ∧
    (∀ i, minusCoefficients coefficients0407 upper0407 i = powerCoefficients10 minusWeights0407 i) := by
  decide +kernel

theorem bound0407 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0407 g| ≤ (upper0407 : ℝ) :=
  abs_of_coefficients coefficients0407 upper0407 powerCoefficients10 plusWeights0407 minusWeights0407
    checked0407.1 checked0407.2.1 checked0407.2.2.1 checked0407.2.2.2
    (power_identity10 plusWeights0407) (power_identity10 minusWeights0407) g hg hmax

def envelope0407 : Envelope := ⟨coefficients0407, upper0407, bound0407⟩

def coefficients0408 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/512), (-5/1024), (-5/512), (-45/8192), (-25/16384)]

def upper0408 : ℚ := (60123/6553600000000)

def plusWeights0408 : Fin 11 → ℚ := ![(60123/6553600000000), (60123/655360000000), (541107/1310720000000), (180369/163840000000), (1262583/655360000000), (3787749/1638400000000), (1268983/655360000000), (186689/163840000000), (615859/1310720000000), (423157/3276800000000), (60123/3276800000000)]

def minusWeights0408 : Fin 11 → ℚ := ![(60123/6553600000000), (60123/655360000000), (541107/1310720000000), (180369/163840000000), (1262583/655360000000), (3787749/1638400000000), (1256183/655360000000), (174049/163840000000), (93271/262144000000), (178073/3276800000000), 0]

theorem checked0408 :
    (∀ i, 0 ≤ plusWeights0408 i) ∧
    (∀ i, 0 ≤ minusWeights0408 i) ∧
    (∀ i, plusCoefficients coefficients0408 upper0408 i = powerCoefficients10 plusWeights0408 i) ∧
    (∀ i, minusCoefficients coefficients0408 upper0408 i = powerCoefficients10 minusWeights0408 i) := by
  decide +kernel

theorem bound0408 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0408 g| ≤ (upper0408 : ℝ) :=
  abs_of_coefficients coefficients0408 upper0408 powerCoefficients10 plusWeights0408 minusWeights0408
    checked0408.1 checked0408.2.1 checked0408.2.2.1 checked0408.2.2.2
    (power_identity10 plusWeights0408) (power_identity10 minusWeights0408) g hg hmax

def envelope0408 : Envelope := ⟨coefficients0408, upper0408, bound0408⟩

def coefficients0409 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/512), (5/512), (95/8192), (75/16384), (125/65536)]

def upper0409 : ℚ := (56953/5242880000000)

def plusWeights0409 : Fin 11 → ℚ := ![(56953/5242880000000), (56953/524288000000), (512577/1048576000000), (170859/131072000000), (1196013/524288000000), (3588039/1310720000000), (1201133/524288000000), (176107/131072000000), (2886053/5242880000000), (79093/524288000000), (56953/2621440000000)]

def minusWeights0409 : Fin 11 → ℚ := ![(56953/5242880000000), (56953/524288000000), (512577/1048576000000), (170859/131072000000), (1196013/524288000000), (3588039/1310720000000), (1190893/524288000000), (165611/131072000000), (2239717/5242880000000), (34813/524288000000), 0]

theorem checked0409 :
    (∀ i, 0 ≤ plusWeights0409 i) ∧
    (∀ i, 0 ≤ minusWeights0409 i) ∧
    (∀ i, plusCoefficients coefficients0409 upper0409 i = powerCoefficients10 plusWeights0409 i) ∧
    (∀ i, minusCoefficients coefficients0409 upper0409 i = powerCoefficients10 minusWeights0409 i) := by
  decide +kernel

theorem bound0409 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0409 g| ≤ (upper0409 : ℝ) :=
  abs_of_coefficients coefficients0409 upper0409 powerCoefficients10 plusWeights0409 minusWeights0409
    checked0409.1 checked0409.2.1 checked0409.2.2.1 checked0409.2.2.2
    (power_identity10 plusWeights0409) (power_identity10 minusWeights0409) g hg hmax

def envelope0409 : Envelope := ⟨coefficients0409, upper0409, bound0409⟩

def coefficients0410 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (25/2048), (15/2048), (585/32768), (805/65536), (1855/262144)]

def upper0410 : ℚ := (6884411/524288000000000)

def plusWeights0410 : Fin 11 → ℚ := ![(6884411/524288000000000), (6884411/52428800000000), (61959699/104857600000000), (20653233/13107200000000), (144572631/52428800000000), (433717893/131072000000000), (145212631/52428800000000), (21302833/13107200000000), (69888819/104857600000000), (383159/2097152000000), (6884411/262144000000000)]

def minusWeights0410 : Fin 11 → ℚ := ![(6884411/524288000000000), (6884411/52428800000000), (61959699/104857600000000), (20653233/13107200000000), (144572631/52428800000000), (433717893/131072000000000), (143932631/52428800000000), (20003633/13107200000000), (54030579/104857600000000), (4189847/52428800000000), 0]

theorem checked0410 :
    (∀ i, 0 ≤ plusWeights0410 i) ∧
    (∀ i, 0 ≤ minusWeights0410 i) ∧
    (∀ i, plusCoefficients coefficients0410 upper0410 i = powerCoefficients10 plusWeights0410 i) ∧
    (∀ i, minusCoefficients coefficients0410 upper0410 i = powerCoefficients10 minusWeights0410 i) := by
  decide +kernel

theorem bound0410 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0410 g| ≤ (upper0410 : ℝ) :=
  abs_of_coefficients coefficients0410 upper0410 powerCoefficients10 plusWeights0410 minusWeights0410
    checked0410.1 checked0410.2.1 checked0410.2.2.1 checked0410.2.2.2
    (power_identity10 plusWeights0410) (power_identity10 minusWeights0410) g hg hmax

def envelope0410 : Envelope := ⟨coefficients0410, upper0410, bound0410⟩

def coefficients0411 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (25/2048), (15/2048), (165/8192), (55/4096), (1115/131072)]

def upper0411 : ℚ := (3448543/262144000000000)

def plusWeights0411 : Fin 11 → ℚ := ![(3448543/262144000000000), (3448543/26214400000000), (31036887/52428800000000), (10345629/6553600000000), (72419403/26214400000000), (217258209/65536000000000), (72739403/26214400000000), (10670429/6553600000000), (35002647/52428800000000), (959411/5242880000000), (3448543/131072000000000)]

def minusWeights0411 : Fin 11 → ℚ := ![(3448543/262144000000000), (3448543/26214400000000), (31036887/52428800000000), (10345629/6553600000000), (72419403/26214400000000), (217258209/65536000000000), (72099403/26214400000000), (10020829/6553600000000), (27071127/52428800000000), (2100031/26214400000000), 0]

theorem checked0411 :
    (∀ i, 0 ≤ plusWeights0411 i) ∧
    (∀ i, 0 ≤ minusWeights0411 i) ∧
    (∀ i, plusCoefficients coefficients0411 upper0411 i = powerCoefficients10 plusWeights0411 i) ∧
    (∀ i, minusCoefficients coefficients0411 upper0411 i = powerCoefficients10 minusWeights0411 i) := by
  decide +kernel

theorem bound0411 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0411 g| ≤ (upper0411 : ℝ) :=
  abs_of_coefficients coefficients0411 upper0411 powerCoefficients10 plusWeights0411 minusWeights0411
    checked0411.1 checked0411.2.1 checked0411.2.2.1 checked0411.2.2.2
    (power_identity10 plusWeights0411) (power_identity10 minusWeights0411) g hg hmax

def envelope0411 : Envelope := ⟨coefficients0411, upper0411, bound0411⟩

def coefficients0412 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/2048), (-93/8192), (1749/32768), (1713/65536), (6615/262144)]

def upper0412 : ℚ := (6611667/524288000000000)

def plusWeights0412 : Fin 11 → ℚ := ![(6611667/524288000000000), (6611667/52428800000000), (59505003/104857600000000), (19835001/13107200000000), (138845007/52428800000000), (416535021/131072000000000), (139536207/52428800000000), (20511321/13107200000000), (67498251/104857600000000), (46276227/262144000000000), (6611667/262144000000000)]

def minusWeights0412 : Fin 11 → ℚ := ![(6611667/524288000000000), (6611667/52428800000000), (59505003/104857600000000), (19835001/13107200000000), (138845007/52428800000000), (416535021/131072000000000), (138153807/52428800000000), (19158681/13107200000000), (10302351/20971520000000), (19840443/262144000000000), 0]

theorem checked0412 :
    (∀ i, 0 ≤ plusWeights0412 i) ∧
    (∀ i, 0 ≤ minusWeights0412 i) ∧
    (∀ i, plusCoefficients coefficients0412 upper0412 i = powerCoefficients10 plusWeights0412 i) ∧
    (∀ i, minusCoefficients coefficients0412 upper0412 i = powerCoefficients10 minusWeights0412 i) := by
  decide +kernel

theorem bound0412 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0412 g| ≤ (upper0412 : ℝ) :=
  abs_of_coefficients coefficients0412 upper0412 powerCoefficients10 plusWeights0412 minusWeights0412
    checked0412.1 checked0412.2.1 checked0412.2.2.1 checked0412.2.2.2
    (power_identity10 plusWeights0412) (power_identity10 minusWeights0412) g hg hmax

def envelope0412 : Envelope := ⟨coefficients0412, upper0412, bound0412⟩

def coefficients0413 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/512), (69/4096), (21/2048), (1/128), (15/8192)]

def upper0413 : ℚ := (253411/16384000000000)

def plusWeights0413 : Fin 11 → ℚ := ![(253411/16384000000000), (253411/1638400000000), (2280699/3276800000000), (760233/409600000000), (5321631/1638400000000), (15964893/4096000000000), (5344031/1638400000000), (783323/409600000000), (513279/655360000000), (1758199/8192000000000), (253411/8192000000000)]

def minusWeights0413 : Fin 11 → ℚ := ![(253411/16384000000000), (253411/1638400000000), (2280699/3276800000000), (760233/409600000000), (5321631/1638400000000), (15964893/4096000000000), (5299231/1638400000000), (737143/409600000000), (1995003/3276800000000), (775911/8192000000000), 0]

theorem checked0413 :
    (∀ i, 0 ≤ plusWeights0413 i) ∧
    (∀ i, 0 ≤ minusWeights0413 i) ∧
    (∀ i, plusCoefficients coefficients0413 upper0413 i = powerCoefficients10 plusWeights0413 i) ∧
    (∀ i, minusCoefficients coefficients0413 upper0413 i = powerCoefficients10 minusWeights0413 i) := by
  decide +kernel

theorem bound0413 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0413 g| ≤ (upper0413 : ℝ) :=
  abs_of_coefficients coefficients0413 upper0413 powerCoefficients10 plusWeights0413 minusWeights0413
    checked0413.1 checked0413.2.1 checked0413.2.2.1 checked0413.2.2.2
    (power_identity10 plusWeights0413) (power_identity10 minusWeights0413) g hg hmax

def envelope0413 : Envelope := ⟨coefficients0413, upper0413, bound0413⟩

def coefficients0414 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/512), (163/8192), (33/1024), (61/2048), (15/2048)]

def upper0414 : ℚ := (13119/819200000000)

def plusWeights0414 : Fin 11 → ℚ := ![(13119/819200000000), (13119/81920000000), (118071/163840000000), (39357/20480000000), (275499/81920000000), (826497/204800000000), (276619/81920000000), (162071/81920000000), (662709/819200000000), (453581/2048000000000), (13119/409600000000)]

def minusWeights0414 : Fin 11 → ℚ := ![(13119/819200000000), (13119/81920000000), (118071/163840000000), (39357/20480000000), (275499/81920000000), (826497/204800000000), (274379/81920000000), (30557/16384000000), (518001/819200000000), (202369/2048000000000), 0]

theorem checked0414 :
    (∀ i, 0 ≤ plusWeights0414 i) ∧
    (∀ i, 0 ≤ minusWeights0414 i) ∧
    (∀ i, plusCoefficients coefficients0414 upper0414 i = powerCoefficients10 plusWeights0414 i) ∧
    (∀ i, minusCoefficients coefficients0414 upper0414 i = powerCoefficients10 minusWeights0414 i) := by
  decide +kernel

theorem bound0414 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0414 g| ≤ (upper0414 : ℝ) :=
  abs_of_coefficients coefficients0414 upper0414 powerCoefficients10 plusWeights0414 minusWeights0414
    checked0414.1 checked0414.2.1 checked0414.2.2.1 checked0414.2.2.2
    (power_identity10 plusWeights0414) (power_identity10 minusWeights0414) g hg hmax

def envelope0414 : Envelope := ⟨coefficients0414, upper0414, bound0414⟩

def coefficients0415 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/512), (119/4096), (21/2048), (1/128), (15/8192)]

def upper0415 : ℚ := (273411/16384000000000)

def plusWeights0415 : Fin 11 → ℚ := ![(273411/16384000000000), (273411/1638400000000), (2460699/3276800000000), (820233/409600000000), (5741631/1638400000000), (17224893/4096000000000), (5764031/1638400000000), (843823/409600000000), (551679/655360000000), (1888199/8192000000000), (273411/8192000000000)]

def minusWeights0415 : Fin 11 → ℚ := ![(273411/16384000000000), (273411/1638400000000), (2460699/3276800000000), (820233/409600000000), (5741631/1638400000000), (17224893/4096000000000), (5719231/1638400000000), (796643/409600000000), (2163003/3276800000000), (845911/8192000000000), 0]

theorem checked0415 :
    (∀ i, 0 ≤ plusWeights0415 i) ∧
    (∀ i, 0 ≤ minusWeights0415 i) ∧
    (∀ i, plusCoefficients coefficients0415 upper0415 i = powerCoefficients10 plusWeights0415 i) ∧
    (∀ i, minusCoefficients coefficients0415 upper0415 i = powerCoefficients10 minusWeights0415 i) := by
  decide +kernel

theorem bound0415 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0415 g| ≤ (upper0415 : ℝ) :=
  abs_of_coefficients coefficients0415 upper0415 powerCoefficients10 plusWeights0415 minusWeights0415
    checked0415.1 checked0415.2.1 checked0415.2.2.1 checked0415.2.2.2
    (power_identity10 plusWeights0415) (power_identity10 minusWeights0415) g hg hmax

def envelope0415 : Envelope := ⟨coefficients0415, upper0415, bound0415⟩

end BilayerDressed.CubicQuarticEnvelopes

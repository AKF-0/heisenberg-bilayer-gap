import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0128 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (5/2048), (65/8192), (627/16384), (559/32768), (4365/524288)]

def upper0128 : ℚ := (160027959/1048576000000000)

def plusWeights0128 : Fin 11 → ℚ := ![(160027959/1048576000000000), (160027959/104857600000000), (1440251631/209715200000000), (480083877/26214400000000), (3360587139/104857600000000), (10040801417/262144000000000), (3278923139/104857600000000), (439400677/26214400000000), (1116223087/209715200000000), (397318019/524288000000000), 0]

def minusWeights0128 : Fin 11 → ℚ := ![(160027959/1048576000000000), (160027959/104857600000000), (1440251631/209715200000000), (480083877/26214400000000), (3360587139/104857600000000), (10122721417/262144000000000), (3442251139/104857600000000), (520767077/26214400000000), (70571207/8388608000000), (1202961571/524288000000000), (160027959/524288000000000)]

theorem checked0128 :
    (∀ i, 0 ≤ plusWeights0128 i) ∧
    (∀ i, 0 ≤ minusWeights0128 i) ∧
    (∀ i, plusCoefficients coefficients0128 upper0128 i = powerCoefficients10 plusWeights0128 i) ∧
    (∀ i, minusCoefficients coefficients0128 upper0128 i = powerCoefficients10 minusWeights0128 i) := by
  decide +kernel

theorem bound0128 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0128 g| ≤ (upper0128 : ℝ) :=
  abs_of_coefficients coefficients0128 upper0128 powerCoefficients10 plusWeights0128 minusWeights0128
    checked0128.1 checked0128.2.1 checked0128.2.2.1 checked0128.2.2.2
    (power_identity10 plusWeights0128) (power_identity10 minusWeights0128) g hg hmax

def envelope0128 : Envelope := ⟨coefficients0128, upper0128, bound0128⟩

def coefficients0129 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (1/64), (-21/512), (-13/256), (-425/16384), (-225/32768)]

def upper0129 : ℚ := (380793/2621440000000)

def plusWeights0129 : Fin 11 → ℚ := ![(380793/2621440000000), (380793/262144000000), (3427137/524288000000), (1142379/65536000000), (7996653/262144000000), (23887559/655360000000), (7795949/262144000000), (5219031/327680000000), (66259289/13107200000000), (4721959/6553600000000), 0]

def minusWeights0129 : Fin 11 → ℚ := ![(380793/2621440000000), (380793/262144000000), (3427137/524288000000), (1142379/65536000000), (7996653/262144000000), (24092359/655360000000), (8197357/262144000000), (6204759/327680000000), (105097561/13107200000000), (14317691/6553600000000), (380793/1310720000000)]

theorem checked0129 :
    (∀ i, 0 ≤ plusWeights0129 i) ∧
    (∀ i, 0 ≤ minusWeights0129 i) ∧
    (∀ i, plusCoefficients coefficients0129 upper0129 i = powerCoefficients10 plusWeights0129 i) ∧
    (∀ i, minusCoefficients coefficients0129 upper0129 i = powerCoefficients10 minusWeights0129 i) := by
  decide +kernel

theorem bound0129 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0129 g| ≤ (upper0129 : ℝ) :=
  abs_of_coefficients coefficients0129 upper0129 powerCoefficients10 plusWeights0129 minusWeights0129
    checked0129.1 checked0129.2.1 checked0129.2.2.1 checked0129.2.2.2
    (power_identity10 plusWeights0129) (power_identity10 minusWeights0129) g hg hmax

def envelope0129 : Envelope := ⟨coefficients0129, upper0129, bound0129⟩

def coefficients0130 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (1/64), (61/4096), (1109/16384), (993/32768), (3865/262144)]

def upper0130 : ℚ := (72575659/524288000000000)

def plusWeights0130 : Fin 11 → ℚ := ![(72575659/524288000000000), (72575659/52428800000000), (653180931/104857600000000), (217726977/13107200000000), (1524088839/52428800000000), (4551786517/131072000000000), (1483948039/52428800000000), (198085697/13107200000000), (499710787/104857600000000), (175996319/262144000000000), 0]

def minusWeights0130 : Fin 11 → ℚ := ![(72575659/524288000000000), (72575659/52428800000000), (653180931/104857600000000), (217726977/13107200000000), (1524088839/52428800000000), (4592746517/131072000000000), (1564229639/52428800000000), (237368257/13107200000000), (32266043/4194304000000), (549760271/262144000000000), (72575659/262144000000000)]

theorem checked0130 :
    (∀ i, 0 ≤ plusWeights0130 i) ∧
    (∀ i, 0 ≤ minusWeights0130 i) ∧
    (∀ i, plusCoefficients coefficients0130 upper0130 i = powerCoefficients10 plusWeights0130 i) ∧
    (∀ i, minusCoefficients coefficients0130 upper0130 i = powerCoefficients10 minusWeights0130 i) := by
  decide +kernel

theorem bound0130 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0130 g| ≤ (upper0130 : ℝ) :=
  abs_of_coefficients coefficients0130 upper0130 powerCoefficients10 plusWeights0130 minusWeights0130
    checked0130.1 checked0130.2.1 checked0130.2.2.1 checked0130.2.2.2
    (power_identity10 plusWeights0130) (power_identity10 minusWeights0130) g hg hmax

def envelope0130 : Envelope := ⟨coefficients0130, upper0130, bound0130⟩

def coefficients0131 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (17/512), (-1/4096), (1685/16384), (1605/32768), (4525/131072)]

def upper0131 : ℚ := (6395811/52428800000000)

def plusWeights0131 : Fin 11 → ℚ := ![(6395811/52428800000000), (6395811/5242880000000), (57562299/10485760000000), (19187433/1310720000000), (134312031/5242880000000), (400888093/13107200000000), (130390111/5242880000000), (17313481/1310720000000), (1731091/419430400000), (15033939/26214400000000), 0]

def minusWeights0131 : Fin 11 → ℚ := ![(6395811/52428800000000), (6395811/5242880000000), (57562299/10485760000000), (19187433/1310720000000), (134312031/5242880000000), (404984093/13107200000000), (138233951/5242880000000), (4212277/262144000000), (71847323/10485760000000), (48924171/26214400000000), (6395811/26214400000000)]

theorem checked0131 :
    (∀ i, 0 ≤ plusWeights0131 i) ∧
    (∀ i, 0 ≤ minusWeights0131 i) ∧
    (∀ i, plusCoefficients coefficients0131 upper0131 i = powerCoefficients10 plusWeights0131 i) ∧
    (∀ i, minusCoefficients coefficients0131 upper0131 i = powerCoefficients10 minusWeights0131 i) := by
  decide +kernel

theorem bound0131 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0131 g| ≤ (upper0131 : ℝ) :=
  abs_of_coefficients coefficients0131 upper0131 powerCoefficients10 plusWeights0131 minusWeights0131
    checked0131.1 checked0131.2.1 checked0131.2.2.1 checked0131.2.2.2
    (power_identity10 plusWeights0131) (power_identity10 minusWeights0131) g hg hmax

def envelope0131 : Envelope := ⟨coefficients0131, upper0131, bound0131⟩

def coefficients0132 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (17/512), (-1/4096), (1835/16384), (1755/32768), (5275/131072)]

def upper0132 : ℚ := (6390741/52428800000000)

def plusWeights0132 : Fin 11 → ℚ := ![(6390741/52428800000000), (6390741/5242880000000), (57516669/10485760000000), (19172223/1310720000000), (134205561/5242880000000), (400568683/13107200000000), (130283641/5242880000000), (17298271/1310720000000), (8646521/2097152000000), (15013509/26214400000000), 0]

def minusWeights0132 : Fin 11 → ℚ := ![(6390741/52428800000000), (6390741/5242880000000), (57516669/10485760000000), (19172223/1310720000000), (134205561/5242880000000), (404664683/13107200000000), (138127481/5242880000000), (841847/52428800000), (71800733/10485760000000), (48893901/26214400000000), (6390741/26214400000000)]

theorem checked0132 :
    (∀ i, 0 ≤ plusWeights0132 i) ∧
    (∀ i, 0 ≤ minusWeights0132 i) ∧
    (∀ i, plusCoefficients coefficients0132 upper0132 i = powerCoefficients10 plusWeights0132 i) ∧
    (∀ i, minusCoefficients coefficients0132 upper0132 i = powerCoefficients10 minusWeights0132 i) := by
  decide +kernel

theorem bound0132 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0132 g| ≤ (upper0132 : ℝ) :=
  abs_of_coefficients coefficients0132 upper0132 powerCoefficients10 plusWeights0132 minusWeights0132
    checked0132.1 checked0132.2.1 checked0132.2.2.1 checked0132.2.2.2
    (power_identity10 plusWeights0132) (power_identity10 minusWeights0132) g hg hmax

def envelope0132 : Envelope := ⟨coefficients0132, upper0132, bound0132⟩

def coefficients0133 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (17/512), (-1/4096), (1855/8192), (2265/16384), (24325/131072)]

def upper0133 : ℚ := (6325539/52428800000000)

def plusWeights0133 : Fin 11 → ℚ := ![(6325539/52428800000000), (6325539/5242880000000), (56929851/10485760000000), (18976617/1310720000000), (132836319/5242880000000), (396460957/13107200000000), (128914399/5242880000000), (3420533/262144000000), (42657787/10485760000000), (14749719/26214400000000), 0]

def minusWeights0133 : Fin 11 → ℚ := ![(6325539/52428800000000), (6325539/5242880000000), (56929851/10485760000000), (18976617/1310720000000), (132836319/5242880000000), (400556957/13107200000000), (136758239/5242880000000), (20850569/1310720000000), (14240383/2097152000000), (48505671/26214400000000), (6325539/26214400000000)]

theorem checked0133 :
    (∀ i, 0 ≤ plusWeights0133 i) ∧
    (∀ i, 0 ≤ minusWeights0133 i) ∧
    (∀ i, plusCoefficients coefficients0133 upper0133 i = powerCoefficients10 plusWeights0133 i) ∧
    (∀ i, minusCoefficients coefficients0133 upper0133 i = powerCoefficients10 minusWeights0133 i) := by
  decide +kernel

theorem bound0133 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0133 g| ≤ (upper0133 : ℝ) :=
  abs_of_coefficients coefficients0133 upper0133 powerCoefficients10 plusWeights0133 minusWeights0133
    checked0133.1 checked0133.2.1 checked0133.2.2.1 checked0133.2.2.2
    (power_identity10 plusWeights0133) (power_identity10 minusWeights0133) g hg hmax

def envelope0133 : Envelope := ⟨coefficients0133, upper0133, bound0133⟩

def coefficients0134 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (9/256), (-249/2048), (-319/2048), (-665/4096), (-985/16384)]

def upper0134 : ℚ := (4422957/32768000000000)

def plusWeights0134 : Fin 11 → ℚ := ![(4422957/32768000000000), (4422957/3276800000000), (39806613/6553600000000), (13268871/819200000000), (92882097/3276800000000), (277366291/8192000000000), (90437297/3276800000000), (12094111/819200000000), (6139953/1310720000000), (2193497/3276800000000), 0]

def minusWeights0134 : Fin 11 → ℚ := ![(4422957/32768000000000), (4422957/3276800000000), (39806613/6553600000000), (13268871/819200000000), (92882097/3276800000000), (279926291/8192000000000), (95326897/3276800000000), (14443631/819200000000), (48913461/6553600000000), (6652417/3276800000000), (4422957/16384000000000)]

theorem checked0134 :
    (∀ i, 0 ≤ plusWeights0134 i) ∧
    (∀ i, 0 ≤ minusWeights0134 i) ∧
    (∀ i, plusCoefficients coefficients0134 upper0134 i = powerCoefficients10 plusWeights0134 i) ∧
    (∀ i, minusCoefficients coefficients0134 upper0134 i = powerCoefficients10 minusWeights0134 i) := by
  decide +kernel

theorem bound0134 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0134 g| ≤ (upper0134 : ℝ) :=
  abs_of_coefficients coefficients0134 upper0134 powerCoefficients10 plusWeights0134 minusWeights0134
    checked0134.1 checked0134.2.1 checked0134.2.2.1 checked0134.2.2.2
    (power_identity10 plusWeights0134) (power_identity10 minusWeights0134) g hg hmax

def envelope0134 : Envelope := ⟨coefficients0134, upper0134, bound0134⟩

def coefficients0135 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (9/256), (-57/1024), (-77/1024), (-475/8192), (-325/16384)]

def upper0135 : ℚ := (835401/6553600000000)

def plusWeights0135 : Fin 11 → ℚ := ![(835401/6553600000000), (835401/655360000000), (7518609/1310720000000), (2506203/163840000000), (17543421/655360000000), (52374263/1638400000000), (17054461/655360000000), (2272331/163840000000), (28621077/6553600000000), (2017967/3276800000000), 0]

def minusWeights0135 : Fin 11 → ℚ := ![(835401/6553600000000), (835401/655360000000), (7518609/1310720000000), (2506203/163840000000), (17543421/655360000000), (52886263/1638400000000), (18032381/655360000000), (109603/6553600000), (46565013/6553600000000), (6336043/3276800000000), (835401/3276800000000)]

theorem checked0135 :
    (∀ i, 0 ≤ plusWeights0135 i) ∧
    (∀ i, 0 ≤ minusWeights0135 i) ∧
    (∀ i, plusCoefficients coefficients0135 upper0135 i = powerCoefficients10 plusWeights0135 i) ∧
    (∀ i, minusCoefficients coefficients0135 upper0135 i = powerCoefficients10 minusWeights0135 i) := by
  decide +kernel

theorem bound0135 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0135 g| ≤ (upper0135 : ℝ) :=
  abs_of_coefficients coefficients0135 upper0135 powerCoefficients10 plusWeights0135 minusWeights0135
    checked0135.1 checked0135.2.1 checked0135.2.2.1 checked0135.2.2.2
    (power_identity10 plusWeights0135) (power_identity10 minusWeights0135) g hg hmax

def envelope0135 : Envelope := ⟨coefficients0135, upper0135, bound0135⟩

def coefficients0136 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-7/512), (-11/1024), (-117/4096), (-41/2048), (-255/16384), (-175/32768)]

def upper0136 : ℚ := (78923/524288000000)

def plusWeights0136 : Fin 11 → ℚ := ![(78923/524288000000), (78923/52428800000), (710307/104857600000), (236769/13107200000), (1657383/52428800000), (4954229/131072000000), (8104899/262144000000), (5456209/327680000000), (69908631/13107200000000), (5044889/6553600000000), 0]

def minusWeights0136 : Fin 11 → ℚ := ![(78923/524288000000), (78923/52428800000), (710307/104857600000), (236769/13107200000), (1657383/52428800000), (4990069/131072000000), (8468931/262144000000), (6382241/327680000000), (107668119/13107200000000), (14685861/6553600000000), (78923/262144000000)]

theorem checked0136 :
    (∀ i, 0 ≤ plusWeights0136 i) ∧
    (∀ i, 0 ≤ minusWeights0136 i) ∧
    (∀ i, plusCoefficients coefficients0136 upper0136 i = powerCoefficients10 plusWeights0136 i) ∧
    (∀ i, minusCoefficients coefficients0136 upper0136 i = powerCoefficients10 minusWeights0136 i) := by
  decide +kernel

theorem bound0136 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0136 g| ≤ (upper0136 : ℝ) :=
  abs_of_coefficients coefficients0136 upper0136 powerCoefficients10 plusWeights0136 minusWeights0136
    checked0136.1 checked0136.2.1 checked0136.2.2.1 checked0136.2.2.2
    (power_identity10 plusWeights0136) (power_identity10 minusWeights0136) g hg hmax

def envelope0136 : Envelope := ⟨coefficients0136, upper0136, bound0136⟩

def coefficients0137 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-7/512), (-11/1024), (-107/4096), (-9/512), (-55/4096), (-75/16384)]

def upper0137 : ℚ := (984763/6553600000000)

def plusWeights0137 : Fin 11 → ℚ := ![(984763/6553600000000), (984763/655360000000), (8862867/1310720000000), (2954289/163840000000), (20680023/655360000000), (61816069/1638400000000), (20224983/655360000000), (2722821/163840000000), (34879423/6553600000000), (2516139/3276800000000), 0]

def minusWeights0137 : Fin 11 → ℚ := ![(984763/6553600000000), (984763/655360000000), (8862867/1310720000000), (2954289/163840000000), (20680023/655360000000), (62264069/1638400000000), (21135063/655360000000), (3185757/163840000000), (53749247/6553600000000), (7331491/3276800000000), (984763/3276800000000)]

theorem checked0137 :
    (∀ i, 0 ≤ plusWeights0137 i) ∧
    (∀ i, 0 ≤ minusWeights0137 i) ∧
    (∀ i, plusCoefficients coefficients0137 upper0137 i = powerCoefficients10 plusWeights0137 i) ∧
    (∀ i, minusCoefficients coefficients0137 upper0137 i = powerCoefficients10 minusWeights0137 i) := by
  decide +kernel

theorem bound0137 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0137 g| ≤ (upper0137 : ℝ) :=
  abs_of_coefficients coefficients0137 upper0137 powerCoefficients10 plusWeights0137 minusWeights0137
    checked0137.1 checked0137.2.1 checked0137.2.2.1 checked0137.2.2.2
    (power_identity10 plusWeights0137) (power_identity10 minusWeights0137) g hg hmax

def envelope0137 : Envelope := ⟨coefficients0137, upper0137, bound0137⟩

def coefficients0138 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-7/512), (-11/1024), (-159/8192), (-57/4096), (-235/32768), (-125/65536)]

def upper0138 : ℚ := (3920321/26214400000000)

def plusWeights0138 : Fin 11 → ℚ := ![(3920321/26214400000000), (3920321/2621440000000), (35282889/5242880000000), (11760963/655360000000), (82326741/2621440000000), (246084223/6553600000000), (80506581/2621440000000), (10835531/655360000000), (138728557/26214400000000), (9998343/13107200000000), 0]

def minusWeights0138 : Fin 11 → ℚ := ![(3920321/26214400000000), (3920321/2621440000000), (35282889/5242880000000), (11760963/655360000000), (82326741/2621440000000), (247876223/6553600000000), (84146901/2621440000000), (2537279/131072000000), (214100333/26214400000000), (29204867/13107200000000), (3920321/13107200000000)]

theorem checked0138 :
    (∀ i, 0 ≤ plusWeights0138 i) ∧
    (∀ i, 0 ≤ minusWeights0138 i) ∧
    (∀ i, plusCoefficients coefficients0138 upper0138 i = powerCoefficients10 plusWeights0138 i) ∧
    (∀ i, minusCoefficients coefficients0138 upper0138 i = powerCoefficients10 minusWeights0138 i) := by
  decide +kernel

theorem bound0138 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0138 g| ≤ (upper0138 : ℝ) :=
  abs_of_coefficients coefficients0138 upper0138 powerCoefficients10 plusWeights0138 minusWeights0138
    checked0138.1 checked0138.2.1 checked0138.2.2.1 checked0138.2.2.2
    (power_identity10 plusWeights0138) (power_identity10 minusWeights0138) g hg hmax

def envelope0138 : Envelope := ⟨coefficients0138, upper0138, bound0138⟩

def coefficients0139 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/256), (-29/1024), (-413/8192), (-29/2048), (-1059/32768), (-923/65536)]

def upper0139 : ℚ := (98778903/655360000000000)

def plusWeights0139 : Fin 11 → ℚ := ![(98778903/655360000000000), (98778903/65536000000000), (889010127/131072000000000), (296336709/16384000000000), (2074356963/65536000000000), (6203870889/163840000000000), (2034100963/65536000000000), (275198109/16384000000000), (711137167/131072000000000), (2077721/2621440000000), 0]

def minusWeights0139 : Fin 11 → ℚ := ![(98778903/655360000000000), (98778903/65536000000000), (889010127/131072000000000), (296336709/16384000000000), (2074356963/65536000000000), (6242270889/163840000000000), (2114612963/65536000000000), (317475309/16384000000000), (1066883087/131072000000000), (145614781/65536000000000), (98778903/327680000000000)]

theorem checked0139 :
    (∀ i, 0 ≤ plusWeights0139 i) ∧
    (∀ i, 0 ≤ minusWeights0139 i) ∧
    (∀ i, plusCoefficients coefficients0139 upper0139 i = powerCoefficients10 plusWeights0139 i) ∧
    (∀ i, minusCoefficients coefficients0139 upper0139 i = powerCoefficients10 minusWeights0139 i) := by
  decide +kernel

theorem bound0139 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0139 g| ≤ (upper0139 : ℝ) :=
  abs_of_coefficients coefficients0139 upper0139 powerCoefficients10 plusWeights0139 minusWeights0139
    checked0139.1 checked0139.2.1 checked0139.2.2.1 checked0139.2.2.2
    (power_identity10 plusWeights0139) (power_identity10 minusWeights0139) g hg hmax

def envelope0139 : Envelope := ⟨coefficients0139, upper0139, bound0139⟩

def coefficients0140 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/512), (-3/1024), (-21/8192), (189/16384), (253/32768), (1115/262144)]

def upper0140 : ℚ := (52805649/524288000000000)

def plusWeights0140 : Fin 11 → ℚ := ![(52805649/524288000000000), (52805649/52428800000000), (475250841/104857600000000), (158416947/13107200000000), (1108918629/52428800000000), (3313955887/131072000000000), (1083165029/52428800000000), (145459987/13107200000000), (370939097/104857600000000), (132817149/262144000000000), 0]

def minusWeights0140 : Fin 11 → ℚ := ![(52805649/524288000000000), (52805649/52428800000000), (475250841/104857600000000), (158416947/13107200000000), (1108918629/52428800000000), (3339555887/131072000000000), (1134672229/52428800000000), (171373907/13107200000000), (115912517/20971520000000), (395239341/262144000000000), (52805649/262144000000000)]

theorem checked0140 :
    (∀ i, 0 ≤ plusWeights0140 i) ∧
    (∀ i, 0 ≤ minusWeights0140 i) ∧
    (∀ i, plusCoefficients coefficients0140 upper0140 i = powerCoefficients10 plusWeights0140 i) ∧
    (∀ i, minusCoefficients coefficients0140 upper0140 i = powerCoefficients10 minusWeights0140 i) := by
  decide +kernel

theorem bound0140 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0140 g| ≤ (upper0140 : ℝ) :=
  abs_of_coefficients coefficients0140 upper0140 powerCoefficients10 plusWeights0140 minusWeights0140
    checked0140.1 checked0140.2.1 checked0140.2.2.1 checked0140.2.2.2
    (power_identity10 plusWeights0140) (power_identity10 minusWeights0140) g hg hmax

def envelope0140 : Envelope := ⟨coefficients0140, upper0140, bound0140⟩

def coefficients0141 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/512), (13/2048), (29/4096), (621/32768), (537/65536), (955/262144)]

def upper0141 : ℚ := (47396953/524288000000000)

def plusWeights0141 : Fin 11 → ℚ := ![(47396953/524288000000000), (47396953/52428800000000), (426572577/104857600000000), (142190859/13107200000000), (995336013/52428800000000), (2973208039/131072000000000), (970068813/52428800000000), (129732939/13107200000000), (328408769/104857600000000), (116299073/262144000000000), 0]

def minusWeights0141 : Fin 11 → ℚ := ![(47396953/524288000000000), (47396953/52428800000000), (426572577/104857600000000), (142190859/13107200000000), (995336013/52428800000000), (2998808039/131072000000000), (1020603213/52428800000000), (154648779/13107200000000), (104947277/20971520000000), (357670457/262144000000000), (47396953/262144000000000)]

theorem checked0141 :
    (∀ i, 0 ≤ plusWeights0141 i) ∧
    (∀ i, 0 ≤ minusWeights0141 i) ∧
    (∀ i, plusCoefficients coefficients0141 upper0141 i = powerCoefficients10 plusWeights0141 i) ∧
    (∀ i, minusCoefficients coefficients0141 upper0141 i = powerCoefficients10 minusWeights0141 i) := by
  decide +kernel

theorem bound0141 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0141 g| ≤ (upper0141 : ℝ) :=
  abs_of_coefficients coefficients0141 upper0141 powerCoefficients10 plusWeights0141 minusWeights0141
    checked0141.1 checked0141.2.1 checked0141.2.2.1 checked0141.2.2.2
    (power_identity10 plusWeights0141) (power_identity10 minusWeights0141) g hg hmax

def envelope0141 : Envelope := ⟨coefficients0141, upper0141, bound0141⟩

def coefficients0142 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/512), (23/2048), (49/4096), (269/8192), (31/2048), (1455/131072)]

def upper0142 : ℚ := (22252061/262144000000000)

def plusWeights0142 : Fin 11 → ℚ := ![(22252061/262144000000000), (22252061/26214400000000), (200268549/52428800000000), (66756183/6553600000000), (467293281/26214400000000), (1395479843/65536000000000), (454787681/26214400000000), (60658423/6553600000000), (6112269/2097152000000), (53706769/131072000000000), 0]

def minusWeights0142 : Fin 11 → ℚ := ![(22252061/262144000000000), (22252061/26214400000000), (200268549/52428800000000), (66756183/6553600000000), (467293281/26214400000000), (1408279843/65536000000000), (479798881/26214400000000), (72853943/6553600000000), (247730373/52428800000000), (168813841/131072000000000), (22252061/131072000000000)]

theorem checked0142 :
    (∀ i, 0 ≤ plusWeights0142 i) ∧
    (∀ i, 0 ≤ minusWeights0142 i) ∧
    (∀ i, plusCoefficients coefficients0142 upper0142 i = powerCoefficients10 plusWeights0142 i) ∧
    (∀ i, minusCoefficients coefficients0142 upper0142 i = powerCoefficients10 minusWeights0142 i) := by
  decide +kernel

theorem bound0142 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0142 g| ≤ (upper0142 : ℝ) :=
  abs_of_coefficients coefficients0142 upper0142 powerCoefficients10 plusWeights0142 minusWeights0142
    checked0142.1 checked0142.2.1 checked0142.2.2.1 checked0142.2.2.2
    (power_identity10 plusWeights0142) (power_identity10 minusWeights0142) g hg hmax

def envelope0142 : Envelope := ⟨coefficients0142, upper0142, bound0142⟩

def coefficients0143 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/512), (23/2048), (123/8192), (901/32768), (817/65536), (2035/262144)]

def upper0143 : ℚ := (44373697/524288000000000)

def plusWeights0143 : Fin 11 → ℚ := ![(44373697/524288000000000), (44373697/52428800000000), (399363273/104857600000000), (133121091/13107200000000), (931847637/52428800000000), (2782742911/131072000000000), (906836437/52428800000000), (120929571/13107200000000), (12181201/4194304000000), (106972713/262144000000000), 0]

def minusWeights0143 : Fin 11 → ℚ := ![(44373697/524288000000000), (44373697/52428800000000), (399363273/104857600000000), (133121091/13107200000000), (931847637/52428800000000), (2808342911/131072000000000), (956858837/52428800000000), (145312611/13107200000000), (494196521/104857600000000), (336764257/262144000000000), (44373697/262144000000000)]

theorem checked0143 :
    (∀ i, 0 ≤ plusWeights0143 i) ∧
    (∀ i, 0 ≤ minusWeights0143 i) ∧
    (∀ i, plusCoefficients coefficients0143 upper0143 i = powerCoefficients10 plusWeights0143 i) ∧
    (∀ i, minusCoefficients coefficients0143 upper0143 i = powerCoefficients10 minusWeights0143 i) := by
  decide +kernel

theorem bound0143 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0143 g| ≤ (upper0143 : ℝ) :=
  abs_of_coefficients coefficients0143 upper0143 powerCoefficients10 plusWeights0143 minusWeights0143
    checked0143.1 checked0143.2.1 checked0143.2.2.1 checked0143.2.2.2
    (power_identity10 plusWeights0143) (power_identity10 minusWeights0143) g hg hmax

def envelope0143 : Envelope := ⟨coefficients0143, upper0143, bound0143⟩

def coefficients0144 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/512), (19/1024), (63/8192), (623/16384), (971/32768), (545/32768)]

def upper0144 : ℚ := (5106629/65536000000000)

def plusWeights0144 : Fin 11 → ℚ := ![(5106629/65536000000000), (5106629/6553600000000), (45959661/13107200000000), (15319887/1638400000000), (107239209/6553600000000), (320117627/16384000000000), (104160809/6553600000000), (13842747/1638400000000), (6930817/2621440000000), (3016659/8192000000000), 0]

def minusWeights0144 : Fin 11 → ℚ := ![(5106629/65536000000000), (5106629/6553600000000), (45959661/13107200000000), (15319887/1638400000000), (107239209/6553600000000), (323317627/16384000000000), (110317609/6553600000000), (16797027/1638400000000), (57265237/13107200000000), (19499827/16384000000000), (5106629/32768000000000)]

theorem checked0144 :
    (∀ i, 0 ≤ plusWeights0144 i) ∧
    (∀ i, 0 ≤ minusWeights0144 i) ∧
    (∀ i, plusCoefficients coefficients0144 upper0144 i = powerCoefficients10 plusWeights0144 i) ∧
    (∀ i, minusCoefficients coefficients0144 upper0144 i = powerCoefficients10 minusWeights0144 i) := by
  decide +kernel

theorem bound0144 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0144 g| ≤ (upper0144 : ℝ) :=
  abs_of_coefficients coefficients0144 upper0144 powerCoefficients10 plusWeights0144 minusWeights0144
    checked0144.1 checked0144.2.1 checked0144.2.2.1 checked0144.2.2.2
    (power_identity10 plusWeights0144) (power_identity10 minusWeights0144) g hg hmax

def envelope0144 : Envelope := ⟨coefficients0144, upper0144, bound0144⟩

def coefficients0145 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/128), (-1/1024), (23/8192), (623/32768), (611/65536), (4115/524288)]

def upper0145 : ℚ := (82439641/1048576000000000)

def plusWeights0145 : Fin 11 → ℚ := ![(82439641/1048576000000000), (82439641/104857600000000), (741956769/209715200000000), (247318923/26214400000000), (1731232461/104857600000000), (5173217383/262144000000000), (1690170061/104857600000000), (226743883/26214400000000), (577104481/209715200000000), (205996053/524288000000000), 0]

def minusWeights0145 : Fin 11 → ℚ := ![(82439641/1048576000000000), (82439641/104857600000000), (741956769/209715200000000), (247318923/26214400000000), (1731232461/104857600000000), (5214177383/262144000000000), (1772294861/104857600000000), (267893963/26214400000000), (906809057/209715200000000), (618400357/524288000000000), (82439641/524288000000000)]

theorem checked0145 :
    (∀ i, 0 ≤ plusWeights0145 i) ∧
    (∀ i, 0 ≤ minusWeights0145 i) ∧
    (∀ i, plusCoefficients coefficients0145 upper0145 i = powerCoefficients10 plusWeights0145 i) ∧
    (∀ i, minusCoefficients coefficients0145 upper0145 i = powerCoefficients10 minusWeights0145 i) := by
  decide +kernel

theorem bound0145 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0145 g| ≤ (upper0145 : ℝ) :=
  abs_of_coefficients coefficients0145 upper0145 powerCoefficients10 plusWeights0145 minusWeights0145
    checked0145.1 checked0145.2.1 checked0145.2.2.1 checked0145.2.2.2
    (power_identity10 plusWeights0145) (power_identity10 minusWeights0145) g hg hmax

def envelope0145 : Envelope := ⟨coefficients0145, upper0145, bound0145⟩

def coefficients0146 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/128), (17/1024), (-1/8192), (1835/32768), (1755/65536), (5275/262144)]

def upper0146 : ℚ := (6390741/104857600000000)

def plusWeights0146 : Fin 11 → ℚ := ![(6390741/104857600000000), (6390741/10485760000000), (57516669/20971520000000), (19172223/2621440000000), (134205561/10485760000000), (400568683/26214400000000), (130283641/10485760000000), (17298271/2621440000000), (8646521/4194304000000), (15013509/52428800000000), 0]

def minusWeights0146 : Fin 11 → ℚ := ![(6390741/104857600000000), (6390741/10485760000000), (57516669/20971520000000), (19172223/2621440000000), (134205561/10485760000000), (404664683/26214400000000), (138127481/10485760000000), (841847/104857600000), (71800733/20971520000000), (48893901/52428800000000), (6390741/52428800000000)]

theorem checked0146 :
    (∀ i, 0 ≤ plusWeights0146 i) ∧
    (∀ i, 0 ≤ minusWeights0146 i) ∧
    (∀ i, plusCoefficients coefficients0146 upper0146 i = powerCoefficients10 plusWeights0146 i) ∧
    (∀ i, minusCoefficients coefficients0146 upper0146 i = powerCoefficients10 minusWeights0146 i) := by
  decide +kernel

theorem bound0146 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0146 g| ≤ (upper0146 : ℝ) :=
  abs_of_coefficients coefficients0146 upper0146 powerCoefficients10 plusWeights0146 minusWeights0146
    checked0146.1 checked0146.2.1 checked0146.2.2.1 checked0146.2.2.2
    (power_identity10 plusWeights0146) (power_identity10 minusWeights0146) g hg hmax

def envelope0146 : Envelope := ⟨coefficients0146, upper0146, bound0146⟩

def coefficients0147 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/128), (9/512), (-31/1024), (-41/1024), (-255/8192), (-175/16384)]

def upper0147 : ℚ := (16779/262144000000)

def plusWeights0147 : Fin 11 → ℚ := ![(16779/262144000000), (16779/26214400000), (151011/52428800000), (50337/6553600000), (352359/26214400000), (1051957/65536000000), (1712899/131072000000), (1141449/163840000000), (14385431/6553600000000), (1015289/3276800000000), 0]

def minusWeights0147 : Fin 11 → ℚ := ![(16779/262144000000), (16779/26214400000), (151011/52428800000), (50337/6553600000), (352359/26214400000), (1062197/65536000000), (1810691/131072000000), (1375401/163840000000), (23367319/6553600000000), (3179461/3276800000000), (16779/131072000000)]

theorem checked0147 :
    (∀ i, 0 ≤ plusWeights0147 i) ∧
    (∀ i, 0 ≤ minusWeights0147 i) ∧
    (∀ i, plusCoefficients coefficients0147 upper0147 i = powerCoefficients10 plusWeights0147 i) ∧
    (∀ i, minusCoefficients coefficients0147 upper0147 i = powerCoefficients10 minusWeights0147 i) := by
  decide +kernel

theorem bound0147 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0147 g| ≤ (upper0147 : ℝ) :=
  abs_of_coefficients coefficients0147 upper0147 powerCoefficients10 plusWeights0147 minusWeights0147
    checked0147.1 checked0147.2.1 checked0147.2.2.1 checked0147.2.2.2
    (power_identity10 plusWeights0147) (power_identity10 minusWeights0147) g hg hmax

def envelope0147 : Envelope := ⟨coefficients0147, upper0147, bound0147⟩

def coefficients0148 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/512), (5/1024), (-79/8192), (-59/4096), (-85/8192), (-95/32768)]

def upper0148 : ℚ := (3593339/65536000000000)

def plusWeights0148 : Fin 11 → ℚ := ![(3593339/65536000000000), (3593339/6553600000000), (32340051/13107200000000), (10780017/1638400000000), (75460119/6553600000000), (225420357/16384000000000), (73572119/6553600000000), (9850437/1638400000000), (25004243/13107200000000), (1780423/6553600000000), 0]

def minusWeights0148 : Fin 11 → ℚ := ![(3593339/65536000000000), (3593339/6553600000000), (32340051/13107200000000), (10780017/1638400000000), (75460119/6553600000000), (227340357/16384000000000), (77348119/6553600000000), (11709597/1638400000000), (39675859/13107200000000), (1081251/1310720000000), (3593339/32768000000000)]

theorem checked0148 :
    (∀ i, 0 ≤ plusWeights0148 i) ∧
    (∀ i, 0 ≤ minusWeights0148 i) ∧
    (∀ i, plusCoefficients coefficients0148 upper0148 i = powerCoefficients10 plusWeights0148 i) ∧
    (∀ i, minusCoefficients coefficients0148 upper0148 i = powerCoefficients10 minusWeights0148 i) := by
  decide +kernel

theorem bound0148 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0148 g| ≤ (upper0148 : ℝ) :=
  abs_of_coefficients coefficients0148 upper0148 powerCoefficients10 plusWeights0148 minusWeights0148
    checked0148.1 checked0148.2.1 checked0148.2.2.1 checked0148.2.2.2
    (power_identity10 plusWeights0148) (power_identity10 minusWeights0148) g hg hmax

def envelope0148 : Envelope := ⟨coefficients0148, upper0148, bound0148⟩

def coefficients0149 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/256), (-435/2048), (-75/1024), (-1425/8192), (-1275/16384)]

def upper0149 : ℚ := (529191/6553600000000)

def plusWeights0149 : Fin 11 → ℚ := ![(529191/6553600000000), (529191/655360000000), (4762719/1310720000000), (1587573/163840000000), (11113011/655360000000), (33339033/1638400000000), (11074611/655360000000), (1545693/163840000000), (4217439/1310720000000), (332757/655360000000), 0]

def minusWeights0149 : Fin 11 → ℚ := ![(529191/6553600000000), (529191/655360000000), (4762719/1310720000000), (1587573/163840000000), (11113011/655360000000), (33339033/1638400000000), (11151411/655360000000), (1629453/163840000000), (5307999/1310720000000), (1161/1048576000), (529191/3276800000000)]

theorem checked0149 :
    (∀ i, 0 ≤ plusWeights0149 i) ∧
    (∀ i, 0 ≤ minusWeights0149 i) ∧
    (∀ i, plusCoefficients coefficients0149 upper0149 i = powerCoefficients10 plusWeights0149 i) ∧
    (∀ i, minusCoefficients coefficients0149 upper0149 i = powerCoefficients10 minusWeights0149 i) := by
  decide +kernel

theorem bound0149 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0149 g| ≤ (upper0149 : ℝ) :=
  abs_of_coefficients coefficients0149 upper0149 powerCoefficients10 plusWeights0149 minusWeights0149
    checked0149.1 checked0149.2.1 checked0149.2.2.1 checked0149.2.2.2
    (power_identity10 plusWeights0149) (power_identity10 minusWeights0149) g hg hmax

def envelope0149 : Envelope := ⟨coefficients0149, upper0149, bound0149⟩

def coefficients0150 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/256), (-435/4096), (-45/2048), (-915/16384), (-825/32768)]

def upper0150 : ℚ := (182169/2621440000000)

def plusWeights0150 : Fin 11 → ℚ := ![(182169/2621440000000), (182169/262144000000), (1639521/524288000000), (546507/65536000000), (3825549/262144000000), (11476647/655360000000), (3810189/262144000000), (530451/65536000000), (7191909/2621440000000), (2806179/6553600000000), 0]

def minusWeights0150 : Fin 11 → ℚ := ![(182169/2621440000000), (182169/262144000000), (1639521/524288000000), (546507/65536000000), (3825549/262144000000), (11476647/655360000000), (3840909/262144000000), (562563/65536000000), (9203301/2621440000000), (6302271/6553600000000), (182169/1310720000000)]

theorem checked0150 :
    (∀ i, 0 ≤ plusWeights0150 i) ∧
    (∀ i, 0 ≤ minusWeights0150 i) ∧
    (∀ i, plusCoefficients coefficients0150 upper0150 i = powerCoefficients10 plusWeights0150 i) ∧
    (∀ i, minusCoefficients coefficients0150 upper0150 i = powerCoefficients10 minusWeights0150 i) := by
  decide +kernel

theorem bound0150 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0150 g| ≤ (upper0150 : ℝ) :=
  abs_of_coefficients coefficients0150 upper0150 powerCoefficients10 plusWeights0150 minusWeights0150
    checked0150.1 checked0150.2.1 checked0150.2.2.1 checked0150.2.2.2
    (power_identity10 plusWeights0150) (power_identity10 minusWeights0150) g hg hmax

def envelope0150 : Envelope := ⟨coefficients0150, upper0150, bound0150⟩

def coefficients0151 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/512), (-615/4096), (-165/2048), (-1515/8192), (-675/8192)]

def upper0151 : ℚ := (148473/3276800000000)

def plusWeights0151 : Fin 11 → ℚ := ![(148473/3276800000000), (148473/327680000000), (1336257/655360000000), (445419/81920000000), (3117933/327680000000), (9353799/819200000000), (3108333/327680000000), (434589/81920000000), (1191009/655360000000), (236811/819200000000), 0]

def minusWeights0151 : Fin 11 → ℚ := ![(148473/3276800000000), (148473/327680000000), (1336257/655360000000), (445419/81920000000), (3117933/327680000000), (9353799/819200000000), (3127533/327680000000), (456249/81920000000), (296301/131072000000), (252777/409600000000), (148473/1638400000000)]

theorem checked0151 :
    (∀ i, 0 ≤ plusWeights0151 i) ∧
    (∀ i, 0 ≤ minusWeights0151 i) ∧
    (∀ i, plusCoefficients coefficients0151 upper0151 i = powerCoefficients10 plusWeights0151 i) ∧
    (∀ i, minusCoefficients coefficients0151 upper0151 i = powerCoefficients10 minusWeights0151 i) := by
  decide +kernel

theorem bound0151 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0151 g| ≤ (upper0151 : ℝ) :=
  abs_of_coefficients coefficients0151 upper0151 powerCoefficients10 plusWeights0151 minusWeights0151
    checked0151.1 checked0151.2.1 checked0151.2.2.1 checked0151.2.2.2
    (power_identity10 plusWeights0151) (power_identity10 minusWeights0151) g hg hmax

def envelope0151 : Envelope := ⟨coefficients0151, upper0151, bound0151⟩

def coefficients0152 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/512), (-375/4096), (-45/2048), (-645/8192), (-75/2048)]

def upper0152 : ℚ := (12699/327680000000)

def plusWeights0152 : Fin 11 → ℚ := ![(12699/327680000000), (12699/32768000000), (114291/65536000000), (38097/8192000000), (266679/32768000000), (800037/81920000000), (265719/32768000000), (18531/4096000000), (504783/327680000000), (397101/1638400000000), 0]

def minusWeights0152 : Fin 11 → ℚ := ![(12699/327680000000), (12699/32768000000), (114291/65536000000), (38097/8192000000), (266679/32768000000), (800037/81920000000), (267639/32768000000), (9783/2048000000), (638127/327680000000), (872799/1638400000000), (12699/163840000000)]

theorem checked0152 :
    (∀ i, 0 ≤ plusWeights0152 i) ∧
    (∀ i, 0 ≤ minusWeights0152 i) ∧
    (∀ i, plusCoefficients coefficients0152 upper0152 i = powerCoefficients10 plusWeights0152 i) ∧
    (∀ i, minusCoefficients coefficients0152 upper0152 i = powerCoefficients10 minusWeights0152 i) := by
  decide +kernel

theorem bound0152 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0152 g| ≤ (upper0152 : ℝ) :=
  abs_of_coefficients coefficients0152 upper0152 powerCoefficients10 plusWeights0152 minusWeights0152
    checked0152.1 checked0152.2.1 checked0152.2.2.1 checked0152.2.2.2
    (power_identity10 plusWeights0152) (power_identity10 minusWeights0152) g hg hmax

def envelope0152 : Envelope := ⟨coefficients0152, upper0152, bound0152⟩

def coefficients0153 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/512), (-375/4096), (-45/2048), (-1065/16384), (-975/32768)]

def upper0153 : ℚ := (507771/13107200000000)

def plusWeights0153 : Fin 11 → ℚ := ![(507771/13107200000000), (507771/1310720000000), (4569939/2621440000000), (1523313/327680000000), (10663191/1310720000000), (31989573/3276800000000), (10624791/1310720000000), (1481913/327680000000), (4036563/2621440000000), (1587549/6553600000000), 0]

def minusWeights0153 : Fin 11 → ℚ := ![(507771/13107200000000), (507771/1310720000000), (4569939/2621440000000), (1523313/327680000000), (10663191/1310720000000), (31989573/3276800000000), (10701591/1310720000000), (1564713/327680000000), (1020663/524288000000), (3490161/6553600000000), (507771/6553600000000)]

theorem checked0153 :
    (∀ i, 0 ≤ plusWeights0153 i) ∧
    (∀ i, 0 ≤ minusWeights0153 i) ∧
    (∀ i, plusCoefficients coefficients0153 upper0153 i = powerCoefficients10 plusWeights0153 i) ∧
    (∀ i, minusCoefficients coefficients0153 upper0153 i = powerCoefficients10 minusWeights0153 i) := by
  decide +kernel

theorem bound0153 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0153 g| ≤ (upper0153 : ℝ) :=
  abs_of_coefficients coefficients0153 upper0153 powerCoefficients10 plusWeights0153 minusWeights0153
    checked0153.1 checked0153.2.1 checked0153.2.2.1 checked0153.2.2.2
    (power_identity10 plusWeights0153) (power_identity10 minusWeights0153) g hg hmax

def envelope0153 : Envelope := ⟨coefficients0153, upper0153, bound0153⟩

def coefficients0154 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/512), (-435/8192), (-45/4096), (-915/32768), (-825/65536)]

def upper0154 : ℚ := (182169/5242880000000)

def plusWeights0154 : Fin 11 → ℚ := ![(182169/5242880000000), (182169/524288000000), (1639521/1048576000000), (546507/131072000000), (3825549/524288000000), (11476647/1310720000000), (3810189/524288000000), (530451/131072000000), (7191909/5242880000000), (2806179/13107200000000), 0]

def minusWeights0154 : Fin 11 → ℚ := ![(182169/5242880000000), (182169/524288000000), (1639521/1048576000000), (546507/131072000000), (3825549/524288000000), (11476647/1310720000000), (3840909/524288000000), (562563/131072000000), (9203301/5242880000000), (6302271/13107200000000), (182169/2621440000000)]

theorem checked0154 :
    (∀ i, 0 ≤ plusWeights0154 i) ∧
    (∀ i, 0 ≤ minusWeights0154 i) ∧
    (∀ i, plusCoefficients coefficients0154 upper0154 i = powerCoefficients10 plusWeights0154 i) ∧
    (∀ i, minusCoefficients coefficients0154 upper0154 i = powerCoefficients10 minusWeights0154 i) := by
  decide +kernel

theorem bound0154 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0154 g| ≤ (upper0154 : ℝ) :=
  abs_of_coefficients coefficients0154 upper0154 powerCoefficients10 plusWeights0154 minusWeights0154
    checked0154.1 checked0154.2.1 checked0154.2.2.1 checked0154.2.2.2
    (power_identity10 plusWeights0154) (power_identity10 minusWeights0154) g hg hmax

def envelope0154 : Envelope := ⟨coefficients0154, upper0154, bound0154⟩

def coefficients0155 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/512), (-435/8192), (-45/4096), (-765/32768), (-675/65536)]

def upper0155 : ℚ := (910719/26214400000000)

def plusWeights0155 : Fin 11 → ℚ := ![(910719/26214400000000), (910719/2621440000000), (8196471/5242880000000), (2732157/655360000000), (19125099/2621440000000), (57375297/6553600000000), (19048299/2621440000000), (2651877/655360000000), (287631/209715200000), (2805609/13107200000000), 0]

def minusWeights0155 : Fin 11 → ℚ := ![(910719/26214400000000), (910719/2621440000000), (8196471/5242880000000), (2732157/655360000000), (19125099/2621440000000), (57375297/6553600000000), (19201899/2621440000000), (2812437/655360000000), (9202167/5242880000000), (6301581/13107200000000), (910719/13107200000000)]

theorem checked0155 :
    (∀ i, 0 ≤ plusWeights0155 i) ∧
    (∀ i, 0 ≤ minusWeights0155 i) ∧
    (∀ i, plusCoefficients coefficients0155 upper0155 i = powerCoefficients10 plusWeights0155 i) ∧
    (∀ i, minusCoefficients coefficients0155 upper0155 i = powerCoefficients10 minusWeights0155 i) := by
  decide +kernel

theorem bound0155 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0155 g| ≤ (upper0155 : ℝ) :=
  abs_of_coefficients coefficients0155 upper0155 powerCoefficients10 plusWeights0155 minusWeights0155
    checked0155.1 checked0155.2.1 checked0155.2.2.1 checked0155.2.2.2
    (power_identity10 plusWeights0155) (power_identity10 minusWeights0155) g hg hmax

def envelope0155 : Envelope := ⟨coefficients0155, upper0155, bound0155⟩

def coefficients0156 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/512), (-165/4096), (-15/2048), (-255/16384), (-225/32768)]

def upper0156 : ℚ := (437973/13107200000000)

def plusWeights0156 : Fin 11 → ℚ := ![(437973/13107200000000), (437973/1310720000000), (3941757/2621440000000), (1313919/327680000000), (9197433/1310720000000), (27592299/3276800000000), (9159033/1310720000000), (1274199/327680000000), (689817/524288000000), (1341603/6553600000000), 0]

def minusWeights0156 : Fin 11 → ℚ := ![(437973/13107200000000), (437973/1310720000000), (3941757/2621440000000), (1313919/327680000000), (9197433/1310720000000), (27592299/3276800000000), (9235833/1310720000000), (1353639/327680000000), (4434429/2621440000000), (3038127/6553600000000), (437973/6553600000000)]

theorem checked0156 :
    (∀ i, 0 ≤ plusWeights0156 i) ∧
    (∀ i, 0 ≤ minusWeights0156 i) ∧
    (∀ i, plusCoefficients coefficients0156 upper0156 i = powerCoefficients10 plusWeights0156 i) ∧
    (∀ i, minusCoefficients coefficients0156 upper0156 i = powerCoefficients10 minusWeights0156 i) := by
  decide +kernel

theorem bound0156 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0156 g| ≤ (upper0156 : ℝ) :=
  abs_of_coefficients coefficients0156 upper0156 powerCoefficients10 plusWeights0156 minusWeights0156
    checked0156.1 checked0156.2.1 checked0156.2.2.1 checked0156.2.2.2
    (power_identity10 plusWeights0156) (power_identity10 minusWeights0156) g hg hmax

def envelope0156 : Envelope := ⟨coefficients0156, upper0156, bound0156⟩

def coefficients0157 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/1024), (-495/8192), (-105/4096), (-1155/16384), (-525/16384)]

def upper0157 : ℚ := (137763/6553600000000)

def plusWeights0157 : Fin 11 → ℚ := ![(137763/6553600000000), (137763/655360000000), (1239867/1310720000000), (413289/163840000000), (2893023/655360000000), (8679069/1638400000000), (2883423/655360000000), (402699/163840000000), (1100571/1310720000000), (27219/204800000000), 0]

def minusWeights0157 : Fin 11 → ℚ := ![(137763/6553600000000), (137763/655360000000), (1239867/1310720000000), (413289/163840000000), (2893023/655360000000), (8679069/1638400000000), (2902623/655360000000), (423879/163840000000), (1379163/1310720000000), (471063/1638400000000), (137763/3276800000000)]

theorem checked0157 :
    (∀ i, 0 ≤ plusWeights0157 i) ∧
    (∀ i, 0 ≤ minusWeights0157 i) ∧
    (∀ i, plusCoefficients coefficients0157 upper0157 i = powerCoefficients10 plusWeights0157 i) ∧
    (∀ i, minusCoefficients coefficients0157 upper0157 i = powerCoefficients10 minusWeights0157 i) := by
  decide +kernel

theorem bound0157 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0157 g| ≤ (upper0157 : ℝ) :=
  abs_of_coefficients coefficients0157 upper0157 powerCoefficients10 plusWeights0157 minusWeights0157
    checked0157.1 checked0157.2.1 checked0157.2.2.1 checked0157.2.2.2
    (power_identity10 plusWeights0157) (power_identity10 minusWeights0157) g hg hmax

def envelope0157 : Envelope := ⟨coefficients0157, upper0157, bound0157⟩

def coefficients0158 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/1024), (-375/8192), (-45/4096), (-495/16384), (-225/16384)]

def upper0158 : ℚ := (126927/6553600000000)

def plusWeights0158 : Fin 11 → ℚ := ![(126927/6553600000000), (126927/655360000000), (1142343/1310720000000), (380781/163840000000), (2665467/655360000000), (7996401/1638400000000), (2655867/655360000000), (370431/163840000000), (1008999/1310720000000), (24801/204800000000), 0]

def minusWeights0158 : Fin 11 → ℚ := ![(126927/6553600000000), (126927/655360000000), (1142343/1310720000000), (380781/163840000000), (2665467/655360000000), (7996401/1638400000000), (2675067/655360000000), (391131/163840000000), (1275687/1310720000000), (436227/1638400000000), (126927/3276800000000)]

theorem checked0158 :
    (∀ i, 0 ≤ plusWeights0158 i) ∧
    (∀ i, 0 ≤ minusWeights0158 i) ∧
    (∀ i, plusCoefficients coefficients0158 upper0158 i = powerCoefficients10 plusWeights0158 i) ∧
    (∀ i, minusCoefficients coefficients0158 upper0158 i = powerCoefficients10 minusWeights0158 i) := by
  decide +kernel

theorem bound0158 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0158 g| ≤ (upper0158 : ℝ) :=
  abs_of_coefficients coefficients0158 upper0158 powerCoefficients10 plusWeights0158 minusWeights0158
    checked0158.1 checked0158.2.1 checked0158.2.2.1 checked0158.2.2.2
    (power_identity10 plusWeights0158) (power_identity10 minusWeights0158) g hg hmax

def envelope0158 : Envelope := ⟨coefficients0158, upper0158, bound0158⟩

def coefficients0159 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/1024), (-165/8192), (-15/4096), (-305/32768), (-275/65536)]

def upper0159 : ℚ := (87603/5242880000000)

def plusWeights0159 : Fin 11 → ℚ := ![(87603/5242880000000), (87603/524288000000), (788427/1048576000000), (262809/131072000000), (1839663/524288000000), (5518989/1310720000000), (1831983/524288000000), (50973/26214400000), (3449463/5242880000000), (1341793/13107200000000), 0]

def minusWeights0159 : Fin 11 → ℚ := ![(87603/5242880000000), (87603/524288000000), (788427/1048576000000), (262809/131072000000), (1839663/524288000000), (5518989/1310720000000), (1847343/524288000000), (270753/131072000000), (4434807/5242880000000), (3038357/13107200000000), (87603/2621440000000)]

theorem checked0159 :
    (∀ i, 0 ≤ plusWeights0159 i) ∧
    (∀ i, 0 ≤ minusWeights0159 i) ∧
    (∀ i, plusCoefficients coefficients0159 upper0159 i = powerCoefficients10 plusWeights0159 i) ∧
    (∀ i, minusCoefficients coefficients0159 upper0159 i = powerCoefficients10 minusWeights0159 i) := by
  decide +kernel

theorem bound0159 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0159 g| ≤ (upper0159 : ℝ) :=
  abs_of_coefficients coefficients0159 upper0159 powerCoefficients10 plusWeights0159 minusWeights0159
    checked0159.1 checked0159.2.1 checked0159.2.2.1 checked0159.2.2.2
    (power_identity10 plusWeights0159) (power_identity10 minusWeights0159) g hg hmax

def envelope0159 : Envelope := ⟨coefficients0159, upper0159, bound0159⟩

end BilayerDressed.CubicQuarticEnvelopes

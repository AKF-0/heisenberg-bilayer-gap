import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0608 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/256), (-19/1024), (-145/8192), (-17/4096), (-1055/65536), (-955/131072)]

def upper0608 : ℚ := (36063291/262144000000000)

def plusWeights0608 : Fin 11 → ℚ := ![(36063291/262144000000000), (36063291/26214400000000), (324569619/52428800000000), (108189873/6553600000000), (757329111/26214400000000), (2264307333/65536000000000), (741482711/26214400000000), (100011873/6553600000000), (257012243/52428800000000), (18615893/26214400000000), 0]

def minusWeights0608 : Fin 11 → ℚ := ![(36063291/262144000000000), (36063291/26214400000000), (324569619/52428800000000), (108189873/6553600000000), (757329111/26214400000000), (2279667333/65536000000000), (773175511/26214400000000), (116367873/6553600000000), (78425399/10485760000000), (53510689/26214400000000), (36063291/131072000000000)]

theorem checked0608 :
    (∀ i, 0 ≤ plusWeights0608 i) ∧
    (∀ i, 0 ≤ minusWeights0608 i) ∧
    (∀ i, plusCoefficients coefficients0608 upper0608 i = powerCoefficients10 plusWeights0608 i) ∧
    (∀ i, minusCoefficients coefficients0608 upper0608 i = powerCoefficients10 minusWeights0608 i) := by
  decide +kernel

theorem bound0608 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0608 g| ≤ (upper0608 : ℝ) :=
  abs_of_coefficients coefficients0608 upper0608 powerCoefficients10 plusWeights0608 minusWeights0608
    checked0608.1 checked0608.2.1 checked0608.2.2.1 checked0608.2.2.2
    (power_identity10 plusWeights0608) (power_identity10 minusWeights0608) g hg hmax

def envelope0608 : Envelope := ⟨coefficients0608, upper0608, bound0608⟩

def coefficients0609 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/512), (13/2048), (83/8192), (31/2048), (103/16384), (1285/524288)]

def upper0609 : ℚ := (94516031/1048576000000000)

def plusWeights0609 : Fin 11 → ℚ := ![(94516031/1048576000000000), (94516031/104857600000000), (850644279/209715200000000), (283548093/26214400000000), (1984836651/104857600000000), (5928909953/262144000000000), (1934302251/104857600000000), (258640253/26214400000000), (654500663/209715200000000), (231647771/524288000000000), 0]

def minusWeights0609 : Fin 11 → ℚ := ![(94516031/1048576000000000), (94516031/104857600000000), (850644279/209715200000000), (283548093/26214400000000), (1984836651/104857600000000), (5980109953/262144000000000), (2035371051/104857600000000), (308455933/26214400000000), (209357579/41943040000000), (713512539/524288000000000), (94516031/524288000000000)]

theorem checked0609 :
    (∀ i, 0 ≤ plusWeights0609 i) ∧
    (∀ i, 0 ≤ minusWeights0609 i) ∧
    (∀ i, plusCoefficients coefficients0609 upper0609 i = powerCoefficients10 plusWeights0609 i) ∧
    (∀ i, minusCoefficients coefficients0609 upper0609 i = powerCoefficients10 minusWeights0609 i) := by
  decide +kernel

theorem bound0609 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0609 g| ≤ (upper0609 : ℝ) :=
  abs_of_coefficients coefficients0609 upper0609 powerCoefficients10 plusWeights0609 minusWeights0609
    checked0609.1 checked0609.2.1 checked0609.2.2.1 checked0609.2.2.2
    (power_identity10 plusWeights0609) (power_identity10 minusWeights0609) g hg hmax

def envelope0609 : Envelope := ⟨coefficients0609, upper0609, bound0609⟩

def coefficients0610 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/512), (7/1024), (79/8192), (523/32768), (431/65536), (1455/524288)]

def upper0610 : ℚ := (94046253/1048576000000000)

def plusWeights0610 : Fin 11 → ℚ := ![(94046253/1048576000000000), (94046253/104857600000000), (846416277/209715200000000), (282138759/26214400000000), (1974971313/104857600000000), (5899313939/262144000000000), (1924488113/104857600000000), (257280839/26214400000000), (650858069/209715200000000), (230254873/524288000000000), 0]

def minusWeights0610 : Fin 11 → ℚ := ![(94046253/1048576000000000), (94046253/104857600000000), (846416277/209715200000000), (282138759/26214400000000), (1974971313/104857600000000), (5950513939/262144000000000), (2025454513/104857600000000), (306996679/26214400000000), (208394897/41943040000000), (710207657/524288000000000), (94046253/524288000000000)]

theorem checked0610 :
    (∀ i, 0 ≤ plusWeights0610 i) ∧
    (∀ i, 0 ≤ minusWeights0610 i) ∧
    (∀ i, plusCoefficients coefficients0610 upper0610 i = powerCoefficients10 plusWeights0610 i) ∧
    (∀ i, minusCoefficients coefficients0610 upper0610 i = powerCoefficients10 minusWeights0610 i) := by
  decide +kernel

theorem bound0610 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0610 g| ≤ (upper0610 : ℝ) :=
  abs_of_coefficients coefficients0610 upper0610 powerCoefficients10 plusWeights0610 minusWeights0610
    checked0610.1 checked0610.2.1 checked0610.2.2.1 checked0610.2.2.2
    (power_identity10 plusWeights0610) (power_identity10 minusWeights0610) g hg hmax

def envelope0610 : Envelope := ⟨coefficients0610, upper0610, bound0610⟩

def coefficients0611 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/512), (23/2048), (123/8192), (159/8192), (1/128), (1535/524288)]

def upper0611 : ℚ := (88837581/1048576000000000)

def plusWeights0611 : Fin 11 → ℚ := ![(88837581/1048576000000000), (88837581/104857600000000), (799538229/209715200000000), (266512743/26214400000000), (1865589201/104857600000000), (5571167603/262144000000000), (1815566801/104857600000000), (242129703/26214400000000), (609854773/209715200000000), (214309121/524288000000000), 0]

def minusWeights0611 : Fin 11 → ℚ := ![(88837581/1048576000000000), (88837581/104857600000000), (799538229/209715200000000), (266512743/26214400000000), (1865589201/104857600000000), (5622367603/262144000000000), (1915611601/104857600000000), (290895783/26214400000000), (197844337/41943040000000), (674066689/524288000000000), (88837581/524288000000000)]

theorem checked0611 :
    (∀ i, 0 ≤ plusWeights0611 i) ∧
    (∀ i, 0 ≤ minusWeights0611 i) ∧
    (∀ i, plusCoefficients coefficients0611 upper0611 i = powerCoefficients10 plusWeights0611 i) ∧
    (∀ i, minusCoefficients coefficients0611 upper0611 i = powerCoefficients10 minusWeights0611 i) := by
  decide +kernel

theorem bound0611 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0611 g| ≤ (upper0611 : ℝ) :=
  abs_of_coefficients coefficients0611 upper0611 powerCoefficients10 plusWeights0611 minusWeights0611
    checked0611.1 checked0611.2.1 checked0611.2.2.1 checked0611.2.2.2
    (power_identity10 plusWeights0611) (power_identity10 minusWeights0611) g hg hmax

def envelope0611 : Envelope := ⟨coefficients0611, upper0611, bound0611⟩

def coefficients0612 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/512), (19/1024), (63/8192), (33/1024), (107/4096), (205/16384)]

def upper0612 : ℚ := (2555343/32768000000000)

def plusWeights0612 : Fin 11 → ℚ := ![(2555343/32768000000000), (2555343/3276800000000), (22998087/6553600000000), (7666029/819200000000), (53662203/3276800000000), (160186609/8192000000000), (52123003/3276800000000), (6927459/819200000000), (17344919/6553600000000), (6041503/16384000000000), 0]

def minusWeights0612 : Fin 11 → ℚ := ![(2555343/32768000000000), (2555343/3276800000000), (22998087/6553600000000), (7666029/819200000000), (53662203/3276800000000), (161786609/8192000000000), (55201403/3276800000000), (8404599/819200000000), (5730251/1310720000000), (19511927/16384000000000), (2555343/16384000000000)]

theorem checked0612 :
    (∀ i, 0 ≤ plusWeights0612 i) ∧
    (∀ i, 0 ≤ minusWeights0612 i) ∧
    (∀ i, plusCoefficients coefficients0612 upper0612 i = powerCoefficients10 plusWeights0612 i) ∧
    (∀ i, minusCoefficients coefficients0612 upper0612 i = powerCoefficients10 minusWeights0612 i) := by
  decide +kernel

theorem bound0612 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0612 g| ≤ (upper0612 : ℝ) :=
  abs_of_coefficients coefficients0612 upper0612 powerCoefficients10 plusWeights0612 minusWeights0612
    checked0612.1 checked0612.2.1 checked0612.2.2.1 checked0612.2.2.2
    (power_identity10 plusWeights0612) (power_identity10 minusWeights0612) g hg hmax

def envelope0612 : Envelope := ⟨coefficients0612, upper0612, bound0612⟩

def coefficients0613 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/128), (1/128), (-21/1024), (-13/512), (-425/32768), (-225/65536)]

def upper0613 : ℚ := (380793/5242880000000)

def plusWeights0613 : Fin 11 → ℚ := ![(380793/5242880000000), (380793/524288000000), (3427137/1048576000000), (1142379/131072000000), (7996653/524288000000), (23887559/1310720000000), (7795949/524288000000), (5219031/655360000000), (66259289/26214400000000), (4721959/13107200000000), 0]

def minusWeights0613 : Fin 11 → ℚ := ![(380793/5242880000000), (380793/524288000000), (3427137/1048576000000), (1142379/131072000000), (7996653/524288000000), (24092359/1310720000000), (8197357/524288000000), (6204759/655360000000), (105097561/26214400000000), (14317691/13107200000000), (380793/2621440000000)]

theorem checked0613 :
    (∀ i, 0 ≤ plusWeights0613 i) ∧
    (∀ i, 0 ≤ minusWeights0613 i) ∧
    (∀ i, plusCoefficients coefficients0613 upper0613 i = powerCoefficients10 plusWeights0613 i) ∧
    (∀ i, minusCoefficients coefficients0613 upper0613 i = powerCoefficients10 minusWeights0613 i) := by
  decide +kernel

theorem bound0613 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0613 g| ≤ (upper0613 : ℝ) :=
  abs_of_coefficients coefficients0613 upper0613 powerCoefficients10 plusWeights0613 minusWeights0613
    checked0613.1 checked0613.2.1 checked0613.2.2.1 checked0613.2.2.2
    (power_identity10 plusWeights0613) (power_identity10 minusWeights0613) g hg hmax

def envelope0613 : Envelope := ⟨coefficients0613, upper0613, bound0613⟩

def coefficients0614 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/128), (1/128), (61/8192), (1109/32768), (993/65536), (3865/524288)]

def upper0614 : ℚ := (72575659/1048576000000000)

def plusWeights0614 : Fin 11 → ℚ := ![(72575659/1048576000000000), (72575659/104857600000000), (653180931/209715200000000), (217726977/26214400000000), (1524088839/104857600000000), (4551786517/262144000000000), (1483948039/104857600000000), (198085697/26214400000000), (499710787/209715200000000), (175996319/524288000000000), 0]

def minusWeights0614 : Fin 11 → ℚ := ![(72575659/1048576000000000), (72575659/104857600000000), (653180931/209715200000000), (217726977/26214400000000), (1524088839/104857600000000), (4592746517/262144000000000), (1564229639/104857600000000), (237368257/26214400000000), (32266043/8388608000000), (549760271/524288000000000), (72575659/524288000000000)]

theorem checked0614 :
    (∀ i, 0 ≤ plusWeights0614 i) ∧
    (∀ i, 0 ≤ minusWeights0614 i) ∧
    (∀ i, plusCoefficients coefficients0614 upper0614 i = powerCoefficients10 plusWeights0614 i) ∧
    (∀ i, minusCoefficients coefficients0614 upper0614 i = powerCoefficients10 minusWeights0614 i) := by
  decide +kernel

theorem bound0614 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0614 g| ≤ (upper0614 : ℝ) :=
  abs_of_coefficients coefficients0614 upper0614 powerCoefficients10 plusWeights0614 minusWeights0614
    checked0614.1 checked0614.2.1 checked0614.2.2.1 checked0614.2.2.2
    (power_identity10 plusWeights0614) (power_identity10 minusWeights0614) g hg hmax

def envelope0614 : Envelope := ⟨coefficients0614, upper0614, bound0614⟩

def coefficients0615 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/128), (17/1024), (-1/8192), (1585/32768), (1405/65536), (5275/524288)]

def upper0615 : ℚ := (12798813/209715200000000)

def plusWeights0615 : Fin 11 → ℚ := ![(12798813/209715200000000), (12798813/20971520000000), (115189317/41943040000000), (38396439/5242880000000), (268775073/20971520000000), (802229219/52428800000000), (260931233/20971520000000), (6929707/1048576000000), (86617989/41943040000000), (30097113/104857600000000), 0]

def minusWeights0615 : Fin 11 → ℚ := ![(12798813/209715200000000), (12798813/20971520000000), (115189317/41943040000000), (38396439/5242880000000), (268775073/20971520000000), (810421219/52428800000000), (276618913/20971520000000), (42144343/5242880000000), (28752129/8388608000000), (97891017/104857600000000), (12798813/104857600000000)]

theorem checked0615 :
    (∀ i, 0 ≤ plusWeights0615 i) ∧
    (∀ i, 0 ≤ minusWeights0615 i) ∧
    (∀ i, plusCoefficients coefficients0615 upper0615 i = powerCoefficients10 plusWeights0615 i) ∧
    (∀ i, minusCoefficients coefficients0615 upper0615 i = powerCoefficients10 minusWeights0615 i) := by
  decide +kernel

theorem bound0615 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0615 g| ≤ (upper0615 : ℝ) :=
  abs_of_coefficients coefficients0615 upper0615 powerCoefficients10 plusWeights0615 minusWeights0615
    checked0615.1 checked0615.2.1 checked0615.2.2.1 checked0615.2.2.2
    (power_identity10 plusWeights0615) (power_identity10 minusWeights0615) g hg hmax

def envelope0615 : Envelope := ⟨coefficients0615, upper0615, bound0615⟩

def coefficients0616 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/128), (9/512), (-57/2048), (-77/2048), (-325/16384), (-175/32768)]

def upper0616 : ℚ := (33411/524288000000)

def plusWeights0616 : Fin 11 → ℚ := ![(33411/524288000000), (33411/52428800000), (300699/104857600000), (100233/13107200000), (701631/52428800000), (2094653/131072000000), (3410363/262144000000), (2271953/327680000000), (28615407/13107200000000), (2017397/6553600000000), 0]

def minusWeights0616 : Fin 11 → ℚ := ![(33411/524288000000), (33411/52428800000), (300699/104857600000), (100233/13107200000), (701631/52428800000), (2115133/131072000000), (3605947/262144000000), (2739697/327680000000), (46559343/13107200000000), (6335353/6553600000000), (33411/262144000000)]

theorem checked0616 :
    (∀ i, 0 ≤ plusWeights0616 i) ∧
    (∀ i, 0 ≤ minusWeights0616 i) ∧
    (∀ i, plusCoefficients coefficients0616 upper0616 i = powerCoefficients10 plusWeights0616 i) ∧
    (∀ i, minusCoefficients coefficients0616 upper0616 i = powerCoefficients10 minusWeights0616 i) := by
  decide +kernel

theorem bound0616 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0616 g| ≤ (upper0616 : ℝ) :=
  abs_of_coefficients coefficients0616 upper0616 powerCoefficients10 plusWeights0616 minusWeights0616
    checked0616.1 checked0616.2.1 checked0616.2.2.1 checked0616.2.2.2
    (power_identity10 plusWeights0616) (power_identity10 minusWeights0616) g hg hmax

def envelope0616 : Envelope := ⟨coefficients0616, upper0616, bound0616⟩

def coefficients0617 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/512), (-435/8192), (-45/4096), (-1065/32768), (-975/65536)]

def upper0617 : ℚ := (910971/26214400000000)

def plusWeights0617 : Fin 11 → ℚ := ![(910971/26214400000000), (910971/2621440000000), (8198739/5242880000000), (2732913/655360000000), (19130391/2621440000000), (57391173/6553600000000), (19053591/2621440000000), (2652633/655360000000), (7193043/5242880000000), (2806749/13107200000000), 0]

def minusWeights0617 : Fin 11 → ℚ := ![(910971/26214400000000), (910971/2621440000000), (8198739/5242880000000), (2732913/655360000000), (19130391/2621440000000), (57391173/6553600000000), (19207191/2621440000000), (2813193/655360000000), (1840887/1048576000000), (6302961/13107200000000), (910971/13107200000000)]

theorem checked0617 :
    (∀ i, 0 ≤ plusWeights0617 i) ∧
    (∀ i, 0 ≤ minusWeights0617 i) ∧
    (∀ i, plusCoefficients coefficients0617 upper0617 i = powerCoefficients10 plusWeights0617 i) ∧
    (∀ i, minusCoefficients coefficients0617 upper0617 i = powerCoefficients10 minusWeights0617 i) := by
  decide +kernel

theorem bound0617 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0617 g| ≤ (upper0617 : ℝ) :=
  abs_of_coefficients coefficients0617 upper0617 powerCoefficients10 plusWeights0617 minusWeights0617
    checked0617.1 checked0617.2.1 checked0617.2.2.1 checked0617.2.2.2
    (power_identity10 plusWeights0617) (power_identity10 minusWeights0617) g hg hmax

def envelope0617 : Envelope := ⟨coefficients0617, upper0617, bound0617⟩

def coefficients0618 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/1024), (-435/8192), (-75/4096), (-1425/32768), (-1275/65536)]

def upper0618 : ℚ := (529191/26214400000000)

def plusWeights0618 : Fin 11 → ℚ := ![(529191/26214400000000), (529191/2621440000000), (4762719/5242880000000), (1587573/655360000000), (11113011/2621440000000), (33339033/6553600000000), (11074611/2621440000000), (1545693/655360000000), (4217439/5242880000000), (332757/2621440000000), 0]

def minusWeights0618 : Fin 11 → ℚ := ![(529191/26214400000000), (529191/2621440000000), (4762719/5242880000000), (1587573/655360000000), (11113011/2621440000000), (33339033/6553600000000), (11151411/2621440000000), (1629453/655360000000), (5307999/5242880000000), (1161/4194304000), (529191/13107200000000)]

theorem checked0618 :
    (∀ i, 0 ≤ plusWeights0618 i) ∧
    (∀ i, 0 ≤ minusWeights0618 i) ∧
    (∀ i, plusCoefficients coefficients0618 upper0618 i = powerCoefficients10 plusWeights0618 i) ∧
    (∀ i, minusCoefficients coefficients0618 upper0618 i = powerCoefficients10 minusWeights0618 i) := by
  decide +kernel

theorem bound0618 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0618 g| ≤ (upper0618 : ℝ) :=
  abs_of_coefficients coefficients0618 upper0618 powerCoefficients10 plusWeights0618 minusWeights0618
    checked0618.1 checked0618.2.1 checked0618.2.2.1 checked0618.2.2.2
    (power_identity10 plusWeights0618) (power_identity10 minusWeights0618) g hg hmax

def envelope0618 : Envelope := ⟨coefficients0618, upper0618, bound0618⟩

def coefficients0619 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/1024), (-375/8192), (-45/4096), (-915/32768), (-825/65536)]

def upper0619 : ℚ := (101529/5242880000000)

def plusWeights0619 : Fin 11 → ℚ := ![(101529/5242880000000), (101529/524288000000), (913761/1048576000000), (304587/131072000000), (2132109/524288000000), (6396327/1310720000000), (2124429/524288000000), (296307/131072000000), (4035429/5242880000000), (1586979/13107200000000), 0]

def minusWeights0619 : Fin 11 → ℚ := ![(101529/5242880000000), (101529/524288000000), (913761/1048576000000), (304587/131072000000), (2132109/524288000000), (6396327/1310720000000), (2139789/524288000000), (312867/131072000000), (5102181/5242880000000), (3489471/13107200000000), (101529/2621440000000)]

theorem checked0619 :
    (∀ i, 0 ≤ plusWeights0619 i) ∧
    (∀ i, 0 ≤ minusWeights0619 i) ∧
    (∀ i, plusCoefficients coefficients0619 upper0619 i = powerCoefficients10 plusWeights0619 i) ∧
    (∀ i, minusCoefficients coefficients0619 upper0619 i = powerCoefficients10 minusWeights0619 i) := by
  decide +kernel

theorem bound0619 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0619 g| ≤ (upper0619 : ℝ) :=
  abs_of_coefficients coefficients0619 upper0619 powerCoefficients10 plusWeights0619 minusWeights0619
    checked0619.1 checked0619.2.1 checked0619.2.2.1 checked0619.2.2.2
    (power_identity10 plusWeights0619) (power_identity10 minusWeights0619) g hg hmax

def envelope0619 : Envelope := ⟨coefficients0619, upper0619, bound0619⟩

def coefficients0620 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/1024), (-375/8192), (-45/4096), (-765/32768), (-675/65536)]

def upper0620 : ℚ := (507519/26214400000000)

def plusWeights0620 : Fin 11 → ℚ := ![(507519/26214400000000), (507519/2621440000000), (4567671/5242880000000), (1522557/655360000000), (10657899/2621440000000), (31973697/6553600000000), (10619499/2621440000000), (1481157/655360000000), (806859/1048576000000), (1586409/13107200000000), 0]

def minusWeights0620 : Fin 11 → ℚ := ![(507519/26214400000000), (507519/2621440000000), (4567671/5242880000000), (1522557/655360000000), (10657899/2621440000000), (31973697/6553600000000), (10696299/2621440000000), (1563957/655360000000), (5101047/5242880000000), (3488781/13107200000000), (507519/13107200000000)]

theorem checked0620 :
    (∀ i, 0 ≤ plusWeights0620 i) ∧
    (∀ i, 0 ≤ minusWeights0620 i) ∧
    (∀ i, plusCoefficients coefficients0620 upper0620 i = powerCoefficients10 plusWeights0620 i) ∧
    (∀ i, minusCoefficients coefficients0620 upper0620 i = powerCoefficients10 minusWeights0620 i) := by
  decide +kernel

theorem bound0620 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0620 g| ≤ (upper0620 : ℝ) :=
  abs_of_coefficients coefficients0620 upper0620 powerCoefficients10 plusWeights0620 minusWeights0620
    checked0620.1 checked0620.2.1 checked0620.2.2.1 checked0620.2.2.2
    (power_identity10 plusWeights0620) (power_identity10 minusWeights0620) g hg hmax

def envelope0620 : Envelope := ⟨coefficients0620, upper0620, bound0620⟩

def coefficients0621 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-15/1024), (-165/8192), (-15/4096), (-255/32768), (-225/65536)]

def upper0621 : ℚ := (437973/26214400000000)

def plusWeights0621 : Fin 11 → ℚ := ![(437973/26214400000000), (437973/2621440000000), (3941757/5242880000000), (1313919/655360000000), (9197433/2621440000000), (27592299/6553600000000), (9159033/2621440000000), (1274199/655360000000), (689817/1048576000000), (1341603/13107200000000), 0]

def minusWeights0621 : Fin 11 → ℚ := ![(437973/26214400000000), (437973/2621440000000), (3941757/5242880000000), (1313919/655360000000), (9197433/2621440000000), (27592299/6553600000000), (9235833/2621440000000), (1353639/655360000000), (4434429/5242880000000), (3038127/13107200000000), (437973/13107200000000)]

theorem checked0621 :
    (∀ i, 0 ≤ plusWeights0621 i) ∧
    (∀ i, 0 ≤ minusWeights0621 i) ∧
    (∀ i, plusCoefficients coefficients0621 upper0621 i = powerCoefficients10 plusWeights0621 i) ∧
    (∀ i, minusCoefficients coefficients0621 upper0621 i = powerCoefficients10 minusWeights0621 i) := by
  decide +kernel

theorem bound0621 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0621 g| ≤ (upper0621 : ℝ) :=
  abs_of_coefficients coefficients0621 upper0621 powerCoefficients10 plusWeights0621 minusWeights0621
    checked0621.1 checked0621.2.1 checked0621.2.2.1 checked0621.2.2.2
    (power_identity10 plusWeights0621) (power_identity10 minusWeights0621) g hg hmax

def envelope0621 : Envelope := ⟨coefficients0621, upper0621, bound0621⟩

def coefficients0622 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/512), (-145/8192), (-15/4096), (-705/32768), (-675/65536)]

def upper0622 : ℚ := (303951/26214400000000)

def plusWeights0622 : Fin 11 → ℚ := ![(303951/26214400000000), (303951/2621440000000), (2735559/5242880000000), (911853/655360000000), (6382971/2621440000000), (19148913/6553600000000), (6357371/2621440000000), (885093/655360000000), (2400327/5242880000000), (936913/13107200000000), 0]

def minusWeights0622 : Fin 11 → ℚ := ![(303951/26214400000000), (303951/2621440000000), (2735559/5242880000000), (911853/655360000000), (6382971/2621440000000), (19148913/6553600000000), (6408571/2621440000000), (938613/655360000000), (3070791/5242880000000), (2102597/13107200000000), (303951/13107200000000)]

theorem checked0622 :
    (∀ i, 0 ≤ plusWeights0622 i) ∧
    (∀ i, 0 ≤ minusWeights0622 i) ∧
    (∀ i, plusCoefficients coefficients0622 upper0622 i = powerCoefficients10 plusWeights0622 i) ∧
    (∀ i, minusCoefficients coefficients0622 upper0622 i = powerCoefficients10 minusWeights0622 i) := by
  decide +kernel

theorem bound0622 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0622 g| ≤ (upper0622 : ℝ) :=
  abs_of_coefficients coefficients0622 upper0622 powerCoefficients10 plusWeights0622 minusWeights0622
    checked0622.1 checked0622.2.1 checked0622.2.2.1 checked0622.2.2.2
    (power_identity10 plusWeights0622) (power_identity10 minusWeights0622) g hg hmax

def envelope0622 : Envelope := ⟨coefficients0622, upper0622, bound0622⟩

def coefficients0623 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/512), (-145/8192), (-15/4096), (-255/32768), (-225/65536)]

def upper0623 : ℚ := (303573/26214400000000)

def plusWeights0623 : Fin 11 → ℚ := ![(303573/26214400000000), (303573/2621440000000), (2732157/5242880000000), (910719/655360000000), (6375033/2621440000000), (19125099/6553600000000), (6349433/2621440000000), (883959/655360000000), (95877/209715200000), (935203/13107200000000), 0]

def minusWeights0623 : Fin 11 → ℚ := ![(303573/26214400000000), (303573/2621440000000), (2732157/5242880000000), (910719/655360000000), (6375033/2621440000000), (19125099/6553600000000), (6400633/2621440000000), (937479/655360000000), (3067389/5242880000000), (2100527/13107200000000), (303573/13107200000000)]

theorem checked0623 :
    (∀ i, 0 ≤ plusWeights0623 i) ∧
    (∀ i, 0 ≤ minusWeights0623 i) ∧
    (∀ i, plusCoefficients coefficients0623 upper0623 i = powerCoefficients10 plusWeights0623 i) ∧
    (∀ i, minusCoefficients coefficients0623 upper0623 i = powerCoefficients10 minusWeights0623 i) := by
  decide +kernel

theorem bound0623 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0623 g| ≤ (upper0623 : ℝ) :=
  abs_of_coefficients coefficients0623 upper0623 powerCoefficients10 plusWeights0623 minusWeights0623
    checked0623.1 checked0623.2.1 checked0623.2.2.1 checked0623.2.2.2
    (power_identity10 plusWeights0623) (power_identity10 minusWeights0623) g hg hmax

def envelope0623 : Envelope := ⟨coefficients0623, upper0623, bound0623⟩

def coefficients0624 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/1024), (-245/8192), (-75/4096), (-1275/32768), (-1125/65536)]

def upper0624 : ℚ := (42453/5242880000000)

def plusWeights0624 : Fin 11 → ℚ := ![(42453/5242880000000), (42453/524288000000), (382077/1048576000000), (127359/131072000000), (891513/524288000000), (2674539/1310720000000), (888953/524288000000), (124407/131072000000), (341757/1048576000000), (136483/2621440000000), 0]

def minusWeights0624 : Fin 11 → ℚ := ![(42453/5242880000000), (42453/524288000000), (382077/1048576000000), (127359/131072000000), (891513/524288000000), (2674539/1310720000000), (894073/524288000000), (130311/131072000000), (422397/1048576000000), (288047/2621440000000), (42453/2621440000000)]

theorem checked0624 :
    (∀ i, 0 ≤ plusWeights0624 i) ∧
    (∀ i, 0 ≤ minusWeights0624 i) ∧
    (∀ i, plusCoefficients coefficients0624 upper0624 i = powerCoefficients10 plusWeights0624 i) ∧
    (∀ i, minusCoefficients coefficients0624 upper0624 i = powerCoefficients10 minusWeights0624 i) := by
  decide +kernel

theorem bound0624 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0624 g| ≤ (upper0624 : ℝ) :=
  abs_of_coefficients coefficients0624 upper0624 powerCoefficients10 plusWeights0624 minusWeights0624
    checked0624.1 checked0624.2.1 checked0624.2.2.1 checked0624.2.2.2
    (power_identity10 plusWeights0624) (power_identity10 minusWeights0624) g hg hmax

def envelope0624 : Envelope := ⟨coefficients0624, upper0624, bound0624⟩

def coefficients0625 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/1024), (-125/8192), (-15/4096), (-405/32768), (-375/65536)]

def upper0625 : ℚ := (169299/26214400000000)

def plusWeights0625 : Fin 11 → ℚ := ![(169299/26214400000000), (169299/2621440000000), (1523691/5242880000000), (507897/655360000000), (3555279/2621440000000), (10665837/6553600000000), (3542479/2621440000000), (494097/655360000000), (1345899/5242880000000), (529373/13107200000000), 0]

def minusWeights0625 : Fin 11 → ℚ := ![(169299/26214400000000), (169299/2621440000000), (1523691/5242880000000), (507897/655360000000), (3555279/2621440000000), (10665837/6553600000000), (3568079/2621440000000), (521697/655360000000), (1701483/5242880000000), (1163617/13107200000000), (169299/13107200000000)]

theorem checked0625 :
    (∀ i, 0 ≤ plusWeights0625 i) ∧
    (∀ i, 0 ≤ minusWeights0625 i) ∧
    (∀ i, plusCoefficients coefficients0625 upper0625 i = powerCoefficients10 plusWeights0625 i) ∧
    (∀ i, minusCoefficients coefficients0625 upper0625 i = powerCoefficients10 minusWeights0625 i) := by
  decide +kernel

theorem bound0625 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0625 g| ≤ (upper0625 : ℝ) :=
  abs_of_coefficients coefficients0625 upper0625 powerCoefficients10 plusWeights0625 minusWeights0625
    checked0625.1 checked0625.2.1 checked0625.2.2.1 checked0625.2.2.2
    (power_identity10 plusWeights0625) (power_identity10 minusWeights0625) g hg hmax

def envelope0625 : Envelope := ⟨coefficients0625, upper0625, bound0625⟩

def coefficients0626 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/1024), (-125/8192), (-15/4096), (-255/32768), (-225/65536)]

def upper0626 : ℚ := (169173/26214400000000)

def plusWeights0626 : Fin 11 → ℚ := ![(169173/26214400000000), (169173/2621440000000), (1522557/5242880000000), (507519/655360000000), (3552633/2621440000000), (10657899/6553600000000), (3539833/2621440000000), (493719/655360000000), (268953/1048576000000), (528803/13107200000000), 0]

def minusWeights0626 : Fin 11 → ℚ := ![(169173/26214400000000), (169173/2621440000000), (1522557/5242880000000), (507519/655360000000), (3552633/2621440000000), (10657899/6553600000000), (3565433/2621440000000), (521319/655360000000), (1700349/5242880000000), (1162927/13107200000000), (169173/13107200000000)]

theorem checked0626 :
    (∀ i, 0 ≤ plusWeights0626 i) ∧
    (∀ i, 0 ≤ minusWeights0626 i) ∧
    (∀ i, plusCoefficients coefficients0626 upper0626 i = powerCoefficients10 plusWeights0626 i) ∧
    (∀ i, minusCoefficients coefficients0626 upper0626 i = powerCoefficients10 minusWeights0626 i) := by
  decide +kernel

theorem bound0626 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0626 g| ≤ (upper0626 : ℝ) :=
  abs_of_coefficients coefficients0626 upper0626 powerCoefficients10 plusWeights0626 minusWeights0626
    checked0626.1 checked0626.2.1 checked0626.2.2.1 checked0626.2.2.2
    (power_identity10 plusWeights0626) (power_identity10 minusWeights0626) g hg hmax

def envelope0626 : Envelope := ⟨coefficients0626, upper0626, bound0626⟩

def coefficients0627 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/1024), (-55/8192), (-5/4096), (-85/32768), (-75/65536)]

def upper0627 : ℚ := (145991/26214400000000)

def plusWeights0627 : Fin 11 → ℚ := ![(145991/26214400000000), (145991/2621440000000), (1313919/5242880000000), (437973/655360000000), (3065811/2621440000000), (9197433/6553600000000), (3053011/2621440000000), (424733/655360000000), (229939/1048576000000), (447201/13107200000000), 0]

def minusWeights0627 : Fin 11 → ℚ := ![(145991/26214400000000), (145991/2621440000000), (1313919/5242880000000), (437973/655360000000), (3065811/2621440000000), (9197433/6553600000000), (3078611/2621440000000), (451213/655360000000), (1478143/5242880000000), (1012709/13107200000000), (145991/13107200000000)]

theorem checked0627 :
    (∀ i, 0 ≤ plusWeights0627 i) ∧
    (∀ i, 0 ≤ minusWeights0627 i) ∧
    (∀ i, plusCoefficients coefficients0627 upper0627 i = powerCoefficients10 plusWeights0627 i) ∧
    (∀ i, minusCoefficients coefficients0627 upper0627 i = powerCoefficients10 minusWeights0627 i) := by
  decide +kernel

theorem bound0627 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0627 g| ≤ (upper0627 : ℝ) :=
  abs_of_coefficients coefficients0627 upper0627 powerCoefficients10 plusWeights0627 minusWeights0627
    checked0627.1 checked0627.2.1 checked0627.2.2.1 checked0627.2.2.2
    (power_identity10 plusWeights0627) (power_identity10 minusWeights0627) g hg hmax

def envelope0627 : Envelope := ⟨coefficients0627, upper0627, bound0627⟩

def coefficients0628 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-87/2048), (-93/2048), (-243/4096), (-387/16384)]

def upper0628 : ℚ := (780507/163840000000000)

def plusWeights0628 : Fin 11 → ℚ := ![(780507/163840000000000), (780507/16384000000000), (7024563/32768000000000), (2341521/4096000000000), (16390647/16384000000000), (49171941/40960000000000), (16390647/16384000000000), (2324121/4096000000000), (6592083/32768000000000), (111171/3276800000000), 0]

def minusWeights0628 : Fin 11 → ℚ := ![(780507/163840000000000), (780507/16384000000000), (7024563/32768000000000), (2341521/4096000000000), (16390647/16384000000000), (49171941/40960000000000), (16390647/16384000000000), (2358921/4096000000000), (7457043/32768000000000), (1005159/16384000000000), (780507/81920000000000)]

theorem checked0628 :
    (∀ i, 0 ≤ plusWeights0628 i) ∧
    (∀ i, 0 ≤ minusWeights0628 i) ∧
    (∀ i, plusCoefficients coefficients0628 upper0628 i = powerCoefficients10 plusWeights0628 i) ∧
    (∀ i, minusCoefficients coefficients0628 upper0628 i = powerCoefficients10 minusWeights0628 i) := by
  decide +kernel

theorem bound0628 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0628 g| ≤ (upper0628 : ℝ) :=
  abs_of_coefficients coefficients0628 upper0628 powerCoefficients10 plusWeights0628 minusWeights0628
    checked0628.1 checked0628.2.1 checked0628.2.2.1 checked0628.2.2.2
    (power_identity10 plusWeights0628) (power_identity10 minusWeights0628) g hg hmax

def envelope0628 : Envelope := ⟨coefficients0628, upper0628, bound0628⟩

def coefficients0629 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-21/512), (-3/64), (-507/8192), (-399/16384)]

def upper0629 : ℚ := (759339/163840000000000)

def plusWeights0629 : Fin 11 → ℚ := ![(759339/163840000000000), (759339/16384000000000), (6834051/32768000000000), (2278017/4096000000000), (15946119/16384000000000), (47838357/40960000000000), (15946119/16384000000000), (2261217/4096000000000), (6415491/32768000000000), (108273/3276800000000), 0]

def minusWeights0629 : Fin 11 → ℚ := ![(759339/163840000000000), (759339/16384000000000), (6834051/32768000000000), (2278017/4096000000000), (15946119/16384000000000), (47838357/40960000000000), (15946119/16384000000000), (2294817/4096000000000), (7252611/32768000000000), (977313/16384000000000), (759339/81920000000000)]

theorem checked0629 :
    (∀ i, 0 ≤ plusWeights0629 i) ∧
    (∀ i, 0 ≤ minusWeights0629 i) ∧
    (∀ i, plusCoefficients coefficients0629 upper0629 i = powerCoefficients10 plusWeights0629 i) ∧
    (∀ i, minusCoefficients coefficients0629 upper0629 i = powerCoefficients10 minusWeights0629 i) := by
  decide +kernel

theorem bound0629 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0629 g| ≤ (upper0629 : ℝ) :=
  abs_of_coefficients coefficients0629 upper0629 powerCoefficients10 plusWeights0629 minusWeights0629
    checked0629.1 checked0629.2.1 checked0629.2.2.1 checked0629.2.2.2
    (power_identity10 plusWeights0629) (power_identity10 minusWeights0629) g hg hmax

def envelope0629 : Envelope := ⟨coefficients0629, upper0629, bound0629⟩

def coefficients0630 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-21/512), (-3/64), (-639/16384), (-423/32768)]

def upper0630 : ℚ := (1510803/327680000000000)

def plusWeights0630 : Fin 11 → ℚ := ![(1510803/327680000000000), (1510803/32768000000000), (13597227/65536000000000), (4532409/8192000000000), (31726863/32768000000000), (95180589/81920000000000), (31726863/32768000000000), (4498809/8192000000000), (12760107/65536000000000), (215121/6553600000000), 0]

def minusWeights0630 : Fin 11 → ℚ := ![(1510803/327680000000000), (1510803/32768000000000), (13597227/65536000000000), (4532409/8192000000000), (31726863/32768000000000), (95180589/81920000000000), (31726863/32768000000000), (4566009/8192000000000), (14434347/65536000000000), (1946001/32768000000000), (1510803/163840000000000)]

theorem checked0630 :
    (∀ i, 0 ≤ plusWeights0630 i) ∧
    (∀ i, 0 ≤ minusWeights0630 i) ∧
    (∀ i, plusCoefficients coefficients0630 upper0630 i = powerCoefficients10 plusWeights0630 i) ∧
    (∀ i, minusCoefficients coefficients0630 upper0630 i = powerCoefficients10 minusWeights0630 i) := by
  decide +kernel

theorem bound0630 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0630 g| ≤ (upper0630 : ℝ) :=
  abs_of_coefficients coefficients0630 upper0630 powerCoefficients10 plusWeights0630 minusWeights0630
    checked0630.1 checked0630.2.1 checked0630.2.2.1 checked0630.2.2.2
    (power_identity10 plusWeights0630) (power_identity10 minusWeights0630) g hg hmax

def envelope0630 : Envelope := ⟨coefficients0630, upper0630, bound0630⟩

def coefficients0631 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-81/2048), (-99/2048), (-453/8192), (-21/1024)]

def upper0631 : ℚ := (184149/40960000000000)

def plusWeights0631 : Fin 11 → ℚ := ![(184149/40960000000000), (184149/4096000000000), (1657341/8192000000000), (552447/1024000000000), (3867129/4096000000000), (11601387/10240000000000), (3867129/4096000000000), (548397/1024000000000), (1556181/8192000000000), (10509/327680000000), 0]

def minusWeights0631 : Fin 11 → ℚ := ![(184149/40960000000000), (184149/4096000000000), (1657341/8192000000000), (552447/1024000000000), (3867129/4096000000000), (11601387/10240000000000), (3867129/4096000000000), (556497/1024000000000), (1758501/8192000000000), (473871/8192000000000), (184149/20480000000000)]

theorem checked0631 :
    (∀ i, 0 ≤ plusWeights0631 i) ∧
    (∀ i, 0 ≤ minusWeights0631 i) ∧
    (∀ i, plusCoefficients coefficients0631 upper0631 i = powerCoefficients10 plusWeights0631 i) ∧
    (∀ i, minusCoefficients coefficients0631 upper0631 i = powerCoefficients10 minusWeights0631 i) := by
  decide +kernel

theorem bound0631 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0631 g| ≤ (upper0631 : ℝ) :=
  abs_of_coefficients coefficients0631 upper0631 powerCoefficients10 plusWeights0631 minusWeights0631
    checked0631.1 checked0631.2.1 checked0631.2.2.1 checked0631.2.2.2
    (power_identity10 plusWeights0631) (power_identity10 minusWeights0631) g hg hmax

def envelope0631 : Envelope := ⟨coefficients0631, upper0631, bound0631⟩

def coefficients0632 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-315/8192), (-45/4096), (-1215/32768), (-1125/65536)]

def upper0632 : ℚ := (104697/26214400000000)

def plusWeights0632 : Fin 11 → ℚ := ![(104697/26214400000000), (104697/2621440000000), (942273/5242880000000), (314091/655360000000), (2198637/2621440000000), (6595911/6553600000000), (2198637/2621440000000), (311571/655360000000), (881217/5242880000000), (368919/13107200000000), 0]

def minusWeights0632 : Fin 11 → ℚ := ![(104697/26214400000000), (104697/2621440000000), (942273/5242880000000), (314091/655360000000), (2198637/2621440000000), (6595911/6553600000000), (2198637/2621440000000), (316611/655360000000), (1003329/5242880000000), (678051/13107200000000), (104697/13107200000000)]

theorem checked0632 :
    (∀ i, 0 ≤ plusWeights0632 i) ∧
    (∀ i, 0 ≤ minusWeights0632 i) ∧
    (∀ i, plusCoefficients coefficients0632 upper0632 i = powerCoefficients10 plusWeights0632 i) ∧
    (∀ i, minusCoefficients coefficients0632 upper0632 i = powerCoefficients10 minusWeights0632 i) := by
  decide +kernel

theorem bound0632 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0632 g| ≤ (upper0632 : ℝ) :=
  abs_of_coefficients coefficients0632 upper0632 powerCoefficients10 plusWeights0632 minusWeights0632
    checked0632.1 checked0632.2.1 checked0632.2.2.1 checked0632.2.2.2
    (power_identity10 plusWeights0632) (power_identity10 minusWeights0632) g hg hmax

def envelope0632 : Envelope := ⟨coefficients0632, upper0632, bound0632⟩

def coefficients0633 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-315/8192), (-45/4096), (-915/32768), (-825/65536)]

def upper0633 : ℚ := (20889/5242880000000)

def plusWeights0633 : Fin 11 → ℚ := ![(20889/5242880000000), (20889/524288000000), (188001/1048576000000), (62667/131072000000), (438669/524288000000), (1316007/1310720000000), (438669/524288000000), (62163/131072000000), (878949/5242880000000), (367779/13107200000000), 0]

def minusWeights0633 : Fin 11 → ℚ := ![(20889/5242880000000), (20889/524288000000), (188001/1048576000000), (62667/131072000000), (438669/524288000000), (1316007/1310720000000), (438669/524288000000), (63171/131072000000), (1001061/5242880000000), (676671/13107200000000), (20889/2621440000000)]

theorem checked0633 :
    (∀ i, 0 ≤ plusWeights0633 i) ∧
    (∀ i, 0 ≤ minusWeights0633 i) ∧
    (∀ i, plusCoefficients coefficients0633 upper0633 i = powerCoefficients10 plusWeights0633 i) ∧
    (∀ i, minusCoefficients coefficients0633 upper0633 i = powerCoefficients10 minusWeights0633 i) := by
  decide +kernel

theorem bound0633 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0633 g| ≤ (upper0633 : ℝ) :=
  abs_of_coefficients coefficients0633 upper0633 powerCoefficients10 plusWeights0633 minusWeights0633
    checked0633.1 checked0633.2.1 checked0633.2.2.1 checked0633.2.2.2
    (power_identity10 plusWeights0633) (power_identity10 minusWeights0633) g hg hmax

def envelope0633 : Envelope := ⟨coefficients0633, upper0633, bound0633⟩

def coefficients0634 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-315/8192), (-45/4096), (-765/32768), (-675/65536)]

def upper0634 : ℚ := (104319/26214400000000)

def plusWeights0634 : Fin 11 → ℚ := ![(104319/26214400000000), (104319/2621440000000), (938871/5242880000000), (312957/655360000000), (2190699/2621440000000), (6572097/6553600000000), (2190699/2621440000000), (310437/655360000000), (175563/1048576000000), (367209/13107200000000), 0]

def minusWeights0634 : Fin 11 → ℚ := ![(104319/26214400000000), (104319/2621440000000), (938871/5242880000000), (312957/655360000000), (2190699/2621440000000), (6572097/6553600000000), (2190699/2621440000000), (315477/655360000000), (999927/5242880000000), (675981/13107200000000), (104319/13107200000000)]

theorem checked0634 :
    (∀ i, 0 ≤ plusWeights0634 i) ∧
    (∀ i, 0 ≤ minusWeights0634 i) ∧
    (∀ i, plusCoefficients coefficients0634 upper0634 i = powerCoefficients10 plusWeights0634 i) ∧
    (∀ i, minusCoefficients coefficients0634 upper0634 i = powerCoefficients10 minusWeights0634 i) := by
  decide +kernel

theorem bound0634 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0634 g| ≤ (upper0634 : ℝ) :=
  abs_of_coefficients coefficients0634 upper0634 powerCoefficients10 plusWeights0634 minusWeights0634
    checked0634.1 checked0634.2.1 checked0634.2.2.1 checked0634.2.2.2
    (power_identity10 plusWeights0634) (power_identity10 minusWeights0634) g hg hmax

def envelope0634 : Envelope := ⟨coefficients0634, upper0634, bound0634⟩

def coefficients0635 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/2048), (-85/2048), (-2385/32768), (-2005/65536)]

def upper0635 : ℚ := (544341/131072000000000)

def plusWeights0635 : Fin 11 → ℚ := ![(544341/131072000000000), (544341/13107200000000), (4899069/26214400000000), (1633023/3276800000000), (11431161/13107200000000), (34293483/32768000000000), (11431161/13107200000000), (1621023/3276800000000), (4600189/26214400000000), (388507/13107200000000), 0]

def minusWeights0635 : Fin 11 → ℚ := ![(544341/131072000000000), (544341/13107200000000), (4899069/26214400000000), (1633023/3276800000000), (11431161/13107200000000), (34293483/32768000000000), (11431161/13107200000000), (1645023/3276800000000), (5197949/26214400000000), (28007/524288000000), (544341/65536000000000)]

theorem checked0635 :
    (∀ i, 0 ≤ plusWeights0635 i) ∧
    (∀ i, 0 ≤ minusWeights0635 i) ∧
    (∀ i, plusCoefficients coefficients0635 upper0635 i = powerCoefficients10 plusWeights0635 i) ∧
    (∀ i, minusCoefficients coefficients0635 upper0635 i = powerCoefficients10 minusWeights0635 i) := by
  decide +kernel

theorem bound0635 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0635 g| ≤ (upper0635 : ℝ) :=
  abs_of_coefficients coefficients0635 upper0635 powerCoefficients10 plusWeights0635 minusWeights0635
    checked0635.1 checked0635.2.1 checked0635.2.2.1 checked0635.2.2.2
    (power_identity10 plusWeights0635) (power_identity10 minusWeights0635) g hg hmax

def envelope0635 : Envelope := ⟨coefficients0635, upper0635, bound0635⟩

def coefficients0636 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-37/1024), (-43/1024), (-1713/32768), (-1321/65536)]

def upper0636 : ℚ := (2678781/655360000000000)

def plusWeights0636 : Fin 11 → ℚ := ![(2678781/655360000000000), (2678781/65536000000000), (24109029/131072000000000), (8036343/16384000000000), (56254401/65536000000000), (168763203/163840000000000), (56254401/65536000000000), (7977143/16384000000000), (22633189/131072000000000), (381983/13107200000000), 0]

def minusWeights0636 : Fin 11 → ℚ := ![(2678781/655360000000000), (2678781/65536000000000), (24109029/131072000000000), (8036343/16384000000000), (56254401/65536000000000), (168763203/163840000000000), (56254401/65536000000000), (8095543/16384000000000), (25584869/131072000000000), (3447647/65536000000000), (2678781/327680000000000)]

theorem checked0636 :
    (∀ i, 0 ≤ plusWeights0636 i) ∧
    (∀ i, 0 ≤ minusWeights0636 i) ∧
    (∀ i, plusCoefficients coefficients0636 upper0636 i = powerCoefficients10 plusWeights0636 i) ∧
    (∀ i, minusCoefficients coefficients0636 upper0636 i = powerCoefficients10 minusWeights0636 i) := by
  decide +kernel

theorem bound0636 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0636 g| ≤ (upper0636 : ℝ) :=
  abs_of_coefficients coefficients0636 upper0636 powerCoefficients10 plusWeights0636 minusWeights0636
    checked0636.1 checked0636.2.1 checked0636.2.2.1 checked0636.2.2.2
    (power_identity10 plusWeights0636) (power_identity10 minusWeights0636) g hg hmax

def envelope0636 : Envelope := ⟨coefficients0636, upper0636, bound0636⟩

def coefficients0637 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-279/8192), (-33/4096), (-2379/65536), (-2223/131072)]

def upper0637 : ℚ := (4619403/1310720000000000)

def plusWeights0637 : Fin 11 → ℚ := ![(4619403/1310720000000000), (4619403/131072000000000), (41574627/262144000000000), (13858209/32768000000000), (97007463/131072000000000), (291022389/327680000000000), (97007463/131072000000000), (13746609/32768000000000), (38875107/262144000000000), (130173/5242880000000), 0]

def minusWeights0637 : Fin 11 → ℚ := ![(4619403/1310720000000000), (4619403/131072000000000), (41574627/262144000000000), (13858209/32768000000000), (97007463/131072000000000), (291022389/327680000000000), (97007463/131072000000000), (13969809/32768000000000), (44274147/262144000000000), (5984481/131072000000000), (4619403/655360000000000)]

theorem checked0637 :
    (∀ i, 0 ≤ plusWeights0637 i) ∧
    (∀ i, 0 ≤ minusWeights0637 i) ∧
    (∀ i, plusCoefficients coefficients0637 upper0637 i = powerCoefficients10 plusWeights0637 i) ∧
    (∀ i, minusCoefficients coefficients0637 upper0637 i = powerCoefficients10 minusWeights0637 i) := by
  decide +kernel

theorem bound0637 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0637 g| ≤ (upper0637 : ℝ) :=
  abs_of_coefficients coefficients0637 upper0637 powerCoefficients10 plusWeights0637 minusWeights0637
    checked0637.1 checked0637.2.1 checked0637.2.2.1 checked0637.2.2.2
    (power_identity10 plusWeights0637) (power_identity10 minusWeights0637) g hg hmax

def envelope0637 : Envelope := ⟨coefficients0637, upper0637, bound0637⟩

def coefficients0638 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-69/2048), (-71/2048), (-201/4096), (-329/16384)]

def upper0638 : ℚ := (617169/163840000000000)

def plusWeights0638 : Fin 11 → ℚ := ![(617169/163840000000000), (617169/16384000000000), (5554521/32768000000000), (1851507/4096000000000), (12960549/16384000000000), (38881647/40960000000000), (12960549/16384000000000), (1837707/4096000000000), (5211961/32768000000000), (87881/3276800000000), 0]

def minusWeights0638 : Fin 11 → ℚ := ![(617169/163840000000000), (617169/16384000000000), (5554521/32768000000000), (1851507/4096000000000), (12960549/16384000000000), (38881647/40960000000000), (12960549/16384000000000), (1865307/4096000000000), (5897081/32768000000000), (794933/16384000000000), (617169/81920000000000)]

theorem checked0638 :
    (∀ i, 0 ≤ plusWeights0638 i) ∧
    (∀ i, 0 ≤ minusWeights0638 i) ∧
    (∀ i, plusCoefficients coefficients0638 upper0638 i = powerCoefficients10 plusWeights0638 i) ∧
    (∀ i, minusCoefficients coefficients0638 upper0638 i = powerCoefficients10 minusWeights0638 i) := by
  decide +kernel

theorem bound0638 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0638 g| ≤ (upper0638 : ℝ) :=
  abs_of_coefficients coefficients0638 upper0638 powerCoefficients10 plusWeights0638 minusWeights0638
    checked0638.1 checked0638.2.1 checked0638.2.2.1 checked0638.2.2.2
    (power_identity10 plusWeights0638) (power_identity10 minusWeights0638) g hg hmax

def envelope0638 : Envelope := ⟨coefficients0638, upper0638, bound0638⟩

def coefficients0639 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-1/32), (-19/512), (-337/8192), (-249/16384)]

def upper0639 : ℚ := (579789/163840000000000)

def plusWeights0639 : Fin 11 → ℚ := ![(579789/163840000000000), (579789/16384000000000), (5218101/32768000000000), (1739367/4096000000000), (12175569/16384000000000), (36526707/40960000000000), (12175569/16384000000000), (1726567/4096000000000), (4898741/32768000000000), (82671/3276800000000), 0]

def minusWeights0639 : Fin 11 → ℚ := ![(579789/163840000000000), (579789/16384000000000), (5218101/32768000000000), (1739367/4096000000000), (12175569/16384000000000), (36526707/40960000000000), (12175569/16384000000000), (1752167/4096000000000), (5537461/32768000000000), (746223/16384000000000), (579789/81920000000000)]

theorem checked0639 :
    (∀ i, 0 ≤ plusWeights0639 i) ∧
    (∀ i, 0 ≤ minusWeights0639 i) ∧
    (∀ i, plusCoefficients coefficients0639 upper0639 i = powerCoefficients10 plusWeights0639 i) ∧
    (∀ i, minusCoefficients coefficients0639 upper0639 i = powerCoefficients10 minusWeights0639 i) := by
  decide +kernel

theorem bound0639 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0639 g| ≤ (upper0639 : ℝ) :=
  abs_of_coefficients coefficients0639 upper0639 powerCoefficients10 plusWeights0639 minusWeights0639
    checked0639.1 checked0639.2.1 checked0639.2.2.1 checked0639.2.2.2
    (power_identity10 plusWeights0639) (power_identity10 minusWeights0639) g hg hmax

def envelope0639 : Envelope := ⟨coefficients0639, upper0639, bound0639⟩

end BilayerDressed.CubicQuarticEnvelopes

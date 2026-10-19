import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0640 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-63/2048), (-77/2048), (-319/8192), (-57/4096)]

def upper0640 : ℚ := (35763/10240000000000)

def plusWeights0640 : Fin 11 → ℚ := ![(35763/10240000000000), (35763/1024000000000), (321867/2048000000000), (107289/256000000000), (751023/1024000000000), (2253069/2560000000000), (751023/1024000000000), (213003/512000000000), (302197/2048000000000), (8161/327680000000), 0]

def minusWeights0640 : Fin 11 → ℚ := ![(35763/10240000000000), (35763/1024000000000), (321867/2048000000000), (107289/256000000000), (751023/1024000000000), (2253069/2560000000000), (751023/1024000000000), (216153/512000000000), (341537/2048000000000), (368183/8192000000000), (35763/5120000000000)]

theorem checked0640 :
    (∀ i, 0 ≤ plusWeights0640 i) ∧
    (∀ i, 0 ≤ minusWeights0640 i) ∧
    (∀ i, plusCoefficients coefficients0640 upper0640 i = powerCoefficients10 plusWeights0640 i) ∧
    (∀ i, minusCoefficients coefficients0640 upper0640 i = powerCoefficients10 minusWeights0640 i) := by
  decide +kernel

theorem bound0640 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0640 g| ≤ (upper0640 : ℝ) :=
  abs_of_coefficients coefficients0640 upper0640 powerCoefficients10 plusWeights0640 minusWeights0640
    checked0640.1 checked0640.2.1 checked0640.2.2.1 checked0640.2.2.2
    (power_identity10 plusWeights0640) (power_identity10 minusWeights0640) g hg hmax

def envelope0640 : Envelope := ⟨coefficients0640, upper0640, bound0640⟩

def coefficients0641 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/512), (-15/512), (-1665/32768), (-1425/65536)]

def upper0641 : ℚ := (85869/26214400000000)

def plusWeights0641 : Fin 11 → ℚ := ![(85869/26214400000000), (85869/2621440000000), (772821/5242880000000), (257607/655360000000), (1803249/2621440000000), (5409747/6553600000000), (1803249/2621440000000), (255687/655360000000), (145041/1048576000000), (305799/13107200000000), 0]

def minusWeights0641 : Fin 11 → ℚ := ![(85869/26214400000000), (85869/2621440000000), (772821/5242880000000), (257607/655360000000), (1803249/2621440000000), (5409747/6553600000000), (1803249/2621440000000), (259527/655360000000), (820437/5242880000000), (552891/13107200000000), (85869/13107200000000)]

theorem checked0641 :
    (∀ i, 0 ≤ plusWeights0641 i) ∧
    (∀ i, 0 ≤ minusWeights0641 i) ∧
    (∀ i, plusCoefficients coefficients0641 upper0641 i = powerCoefficients10 plusWeights0641 i) ∧
    (∀ i, minusCoefficients coefficients0641 upper0641 i = powerCoefficients10 minusWeights0641 i) := by
  decide +kernel

theorem bound0641 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0641 g| ≤ (upper0641 : ℝ) :=
  abs_of_coefficients coefficients0641 upper0641 powerCoefficients10 plusWeights0641 minusWeights0641
    checked0641.1 checked0641.2.1 checked0641.2.2.1 checked0641.2.2.2
    (power_identity10 plusWeights0641) (power_identity10 minusWeights0641) g hg hmax

def envelope0641 : Envelope := ⟨coefficients0641, upper0641, bound0641⟩

def coefficients0642 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/512), (-15/512), (-45/1024), (-75/4096)]

def upper0642 : ℚ := (1071/327680000000)

def plusWeights0642 : Fin 11 → ℚ := ![(1071/327680000000), (1071/32768000000), (9639/65536000000), (3213/8192000000), (22491/32768000000), (67473/81920000000), (22491/32768000000), (3189/8192000000), (45219/327680000000), (19059/819200000000), 0]

def minusWeights0642 : Fin 11 → ℚ := ![(1071/327680000000), (1071/32768000000), (9639/65536000000), (3213/8192000000), (22491/32768000000), (67473/81920000000), (22491/32768000000), (3237/8192000000), (51171/327680000000), (34491/819200000000), (1071/163840000000)]

theorem checked0642 :
    (∀ i, 0 ≤ plusWeights0642 i) ∧
    (∀ i, 0 ≤ minusWeights0642 i) ∧
    (∀ i, plusCoefficients coefficients0642 upper0642 i = powerCoefficients10 plusWeights0642 i) ∧
    (∀ i, minusCoefficients coefficients0642 upper0642 i = powerCoefficients10 minusWeights0642 i) := by
  decide +kernel

theorem bound0642 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0642 g| ≤ (upper0642 : ℝ) :=
  abs_of_coefficients coefficients0642 upper0642 powerCoefficients10 plusWeights0642 minusWeights0642
    checked0642.1 checked0642.2.1 checked0642.2.2.1 checked0642.2.2.2
    (power_identity10 plusWeights0642) (power_identity10 minusWeights0642) g hg hmax

def envelope0642 : Envelope := ⟨coefficients0642, upper0642, bound0642⟩

def coefficients0643 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/8192), 0, (-1125/65536), (-1125/131072)]

def upper0643 : ℚ := (28989/10485760000000)

def plusWeights0643 : Fin 11 → ℚ := ![(28989/10485760000000), (28989/1048576000000), (260901/2097152000000), (86967/262144000000), (608769/1048576000000), (1826307/2621440000000), (608769/1048576000000), (86247/262144000000), (243621/2097152000000), (20331/1048576000000), 0]

def minusWeights0643 : Fin 11 → ℚ := ![(28989/10485760000000), (28989/1048576000000), (260901/2097152000000), (86967/262144000000), (608769/1048576000000), (1826307/2621440000000), (608769/1048576000000), (87687/262144000000), (278181/2097152000000), (37647/1048576000000), (28989/5242880000000)]

theorem checked0643 :
    (∀ i, 0 ≤ plusWeights0643 i) ∧
    (∀ i, 0 ≤ minusWeights0643 i) ∧
    (∀ i, plusCoefficients coefficients0643 upper0643 i = powerCoefficients10 plusWeights0643 i) ∧
    (∀ i, minusCoefficients coefficients0643 upper0643 i = powerCoefficients10 minusWeights0643 i) := by
  decide +kernel

theorem bound0643 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0643 g| ≤ (upper0643 : ℝ) :=
  abs_of_coefficients coefficients0643 upper0643 powerCoefficients10 plusWeights0643 minusWeights0643
    checked0643.1 checked0643.2.1 checked0643.2.2.1 checked0643.2.2.2
    (power_identity10 plusWeights0643) (power_identity10 minusWeights0643) g hg hmax

def envelope0643 : Envelope := ⟨coefficients0643, upper0643, bound0643⟩

def coefficients0644 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/8192), (525/32768), (525/65536), (2625/524288)]

def upper0644 : ℚ := (108123/41943040000000)

def plusWeights0644 : Fin 11 → ℚ := ![(108123/41943040000000), (108123/4194304000000), (973107/8388608000000), (324369/1048576000000), (2270583/4194304000000), (6811749/10485760000000), (2270583/4194304000000), (321489/1048576000000), (905331/8388608000000), (374703/20971520000000), 0]

def minusWeights0644 : Fin 11 → ℚ := ![(108123/41943040000000), (108123/4194304000000), (973107/8388608000000), (324369/1048576000000), (2270583/4194304000000), (6811749/10485760000000), (2270583/4194304000000), (327249/1048576000000), (1040883/8388608000000), (706527/20971520000000), (108123/20971520000000)]

theorem checked0644 :
    (∀ i, 0 ≤ plusWeights0644 i) ∧
    (∀ i, 0 ≤ minusWeights0644 i) ∧
    (∀ i, plusCoefficients coefficients0644 upper0644 i = powerCoefficients10 plusWeights0644 i) ∧
    (∀ i, minusCoefficients coefficients0644 upper0644 i = powerCoefficients10 minusWeights0644 i) := by
  decide +kernel

theorem bound0644 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0644 g| ≤ (upper0644 : ℝ) :=
  abs_of_coefficients coefficients0644 upper0644 powerCoefficients10 plusWeights0644 minusWeights0644
    checked0644.1 checked0644.2.1 checked0644.2.2.1 checked0644.2.2.2
    (power_identity10 plusWeights0644) (power_identity10 minusWeights0644) g hg hmax

def envelope0644 : Envelope := ⟨coefficients0644, upper0644, bound0644⟩

def coefficients0645 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/8192), (675/32768), (675/65536), (3375/524288)]

def upper0645 : ℚ := (106101/41943040000000)

def plusWeights0645 : Fin 11 → ℚ := ![(106101/41943040000000), (106101/4194304000000), (954909/8388608000000), (318303/1048576000000), (2228121/4194304000000), (6684363/10485760000000), (2228121/4194304000000), (315423/1048576000000), (887517/8388608000000), (366561/20971520000000), 0]

def minusWeights0645 : Fin 11 → ℚ := ![(106101/41943040000000), (106101/4194304000000), (954909/8388608000000), (318303/1048576000000), (2228121/4194304000000), (6684363/10485760000000), (2228121/4194304000000), (321183/1048576000000), (1022301/8388608000000), (694449/20971520000000), (106101/20971520000000)]

theorem checked0645 :
    (∀ i, 0 ≤ plusWeights0645 i) ∧
    (∀ i, 0 ≤ minusWeights0645 i) ∧
    (∀ i, plusCoefficients coefficients0645 upper0645 i = powerCoefficients10 plusWeights0645 i) ∧
    (∀ i, minusCoefficients coefficients0645 upper0645 i = powerCoefficients10 minusWeights0645 i) := by
  decide +kernel

theorem bound0645 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0645 g| ≤ (upper0645 : ℝ) :=
  abs_of_coefficients coefficients0645 upper0645 powerCoefficients10 plusWeights0645 minusWeights0645
    checked0645.1 checked0645.2.1 checked0645.2.2.1 checked0645.2.2.2
    (power_identity10 plusWeights0645) (power_identity10 minusWeights0645) g hg hmax

def envelope0645 : Envelope := ⟨coefficients0645, upper0645, bound0645⟩

def coefficients0646 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/8192), (675/32768), (675/65536), (7875/524288)]

def upper0646 : ℚ := (21213/8388608000000)

def plusWeights0646 : Fin 11 → ℚ := ![(21213/8388608000000), (21213/838860800000), (190917/1677721600000), (63639/209715200000), (445473/838860800000), (1336419/2097152000000), (445473/838860800000), (63063/209715200000), (887193/8388608000000), (366381/20971520000000), 0]

def minusWeights0646 : Fin 11 → ℚ := ![(21213/8388608000000), (21213/838860800000), (190917/1677721600000), (63639/209715200000), (445473/838860800000), (1336419/2097152000000), (445473/838860800000), (12843/41943040000), (1021977/8388608000000), (694269/20971520000000), (21213/4194304000000)]

theorem checked0646 :
    (∀ i, 0 ≤ plusWeights0646 i) ∧
    (∀ i, 0 ≤ minusWeights0646 i) ∧
    (∀ i, plusCoefficients coefficients0646 upper0646 i = powerCoefficients10 plusWeights0646 i) ∧
    (∀ i, minusCoefficients coefficients0646 upper0646 i = powerCoefficients10 minusWeights0646 i) := by
  decide +kernel

theorem bound0646 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0646 g| ≤ (upper0646 : ℝ) :=
  abs_of_coefficients coefficients0646 upper0646 powerCoefficients10 plusWeights0646 minusWeights0646
    checked0646.1 checked0646.2.1 checked0646.2.2.1 checked0646.2.2.2
    (power_identity10 plusWeights0646) (power_identity10 minusWeights0646) g hg hmax

def envelope0646 : Envelope := ⟨coefficients0646, upper0646, bound0646⟩

def coefficients0647 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/1024), (-33/1024), (-1833/32768), (-1521/65536)]

def upper0647 : ℚ := (1977381/655360000000000)

def plusWeights0647 : Fin 11 → ℚ := ![(1977381/655360000000000), (1977381/65536000000000), (17796429/131072000000000), (5932143/16384000000000), (41525001/65536000000000), (124575003/163840000000000), (41525001/65536000000000), (5888943/16384000000000), (16717389/131072000000000), (56523/2621440000000), 0]

def minusWeights0647 : Fin 11 → ℚ := ![(1977381/655360000000000), (1977381/65536000000000), (17796429/131072000000000), (5932143/16384000000000), (41525001/65536000000000), (124575003/163840000000000), (41525001/65536000000000), (5975343/16384000000000), (18875469/131072000000000), (2541687/65536000000000), (1977381/327680000000000)]

theorem checked0647 :
    (∀ i, 0 ≤ plusWeights0647 i) ∧
    (∀ i, 0 ≤ minusWeights0647 i) ∧
    (∀ i, plusCoefficients coefficients0647 upper0647 i = powerCoefficients10 plusWeights0647 i) ∧
    (∀ i, minusCoefficients coefficients0647 upper0647 i = powerCoefficients10 minusWeights0647 i) := by
  decide +kernel

theorem bound0647 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0647 g| ≤ (upper0647 : ℝ) :=
  abs_of_coefficients coefficients0647 upper0647 powerCoefficients10 plusWeights0647 minusWeights0647
    checked0647.1 checked0647.2.1 checked0647.2.2.1 checked0647.2.2.2
    (power_identity10 plusWeights0647) (power_identity10 minusWeights0647) g hg hmax

def envelope0647 : Envelope := ⟨coefficients0647, upper0647, bound0647⟩

def coefficients0648 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-205/8192), (5/2048), (-1335/65536), (-1375/131072)]

def upper0648 : ℚ := (131043/52428800000000)

def plusWeights0648 : Fin 11 → ℚ := ![(131043/52428800000000), (131043/5242880000000), (1179387/10485760000000), (393129/1310720000000), (2751903/5242880000000), (8255709/13107200000000), (2751903/5242880000000), (389849/1310720000000), (1100923/10485760000000), (459161/26214400000000), 0]

def minusWeights0648 : Fin 11 → ℚ := ![(131043/52428800000000), (131043/5242880000000), (1179387/10485760000000), (393129/1310720000000), (2751903/5242880000000), (8255709/13107200000000), (2751903/5242880000000), (396409/1310720000000), (1257851/10485760000000), (851269/26214400000000), (131043/26214400000000)]

theorem checked0648 :
    (∀ i, 0 ≤ plusWeights0648 i) ∧
    (∀ i, 0 ≤ minusWeights0648 i) ∧
    (∀ i, plusCoefficients coefficients0648 upper0648 i = powerCoefficients10 plusWeights0648 i) ∧
    (∀ i, minusCoefficients coefficients0648 upper0648 i = powerCoefficients10 minusWeights0648 i) := by
  decide +kernel

theorem bound0648 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0648 g| ≤ (upper0648 : ℝ) :=
  abs_of_coefficients coefficients0648 upper0648 powerCoefficients10 plusWeights0648 minusWeights0648
    checked0648.1 checked0648.2.1 checked0648.2.2.1 checked0648.2.2.2
    (power_identity10 plusWeights0648) (power_identity10 minusWeights0648) g hg hmax

def envelope0648 : Envelope := ⟨coefficients0648, upper0648, bound0648⟩

def coefficients0649 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-205/8192), (5/2048), (-1035/65536), (-1075/131072)]

def upper0649 : ℚ := (130791/52428800000000)

def plusWeights0649 : Fin 11 → ℚ := ![(130791/52428800000000), (130791/5242880000000), (1177119/10485760000000), (392373/1310720000000), (2746611/5242880000000), (8239833/13107200000000), (2746611/5242880000000), (389093/1310720000000), (219731/2097152000000), (458021/26214400000000), 0]

def minusWeights0649 : Fin 11 → ℚ := ![(130791/52428800000000), (130791/5242880000000), (1177119/10485760000000), (392373/1310720000000), (2746611/5242880000000), (8239833/13107200000000), (2746611/5242880000000), (395653/1310720000000), (1255583/10485760000000), (849889/26214400000000), (130791/26214400000000)]

theorem checked0649 :
    (∀ i, 0 ≤ plusWeights0649 i) ∧
    (∀ i, 0 ≤ minusWeights0649 i) ∧
    (∀ i, plusCoefficients coefficients0649 upper0649 i = powerCoefficients10 plusWeights0649 i) ∧
    (∀ i, minusCoefficients coefficients0649 upper0649 i = powerCoefficients10 minusWeights0649 i) := by
  decide +kernel

theorem bound0649 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0649 g| ≤ (upper0649 : ℝ) :=
  abs_of_coefficients coefficients0649 upper0649 powerCoefficients10 plusWeights0649 minusWeights0649
    checked0649.1 checked0649.2.1 checked0649.2.2.1 checked0649.2.2.2
    (power_identity10 plusWeights0649) (power_identity10 minusWeights0649) g hg hmax

def envelope0649 : Envelope := ⟨coefficients0649, upper0649, bound0649⟩

def coefficients0650 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-203/8192), (-19/1024), (-1673/65536), (-1321/131072)]

def upper0650 : ℚ := (3525981/1310720000000000)

def plusWeights0650 : Fin 11 → ℚ := ![(3525981/1310720000000000), (3525981/131072000000000), (31733829/262144000000000), (10577943/32768000000000), (74045601/131072000000000), (222136803/327680000000000), (74045601/131072000000000), (10496743/32768000000000), (29736389/262144000000000), (499919/26214400000000), 0]

def minusWeights0650 : Fin 11 → ℚ := ![(3525981/1310720000000000), (3525981/131072000000000), (31733829/262144000000000), (10577943/32768000000000), (74045601/131072000000000), (222136803/327680000000000), (74045601/131072000000000), (10659143/32768000000000), (33731269/262144000000000), (4552367/131072000000000), (3525981/655360000000000)]

theorem checked0650 :
    (∀ i, 0 ≤ plusWeights0650 i) ∧
    (∀ i, 0 ≤ minusWeights0650 i) ∧
    (∀ i, plusCoefficients coefficients0650 upper0650 i = powerCoefficients10 plusWeights0650 i) ∧
    (∀ i, minusCoefficients coefficients0650 upper0650 i = powerCoefficients10 minusWeights0650 i) := by
  decide +kernel

theorem bound0650 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0650 g| ≤ (upper0650 : ℝ) :=
  abs_of_coefficients coefficients0650 upper0650 powerCoefficients10 plusWeights0650 minusWeights0650
    checked0650.1 checked0650.2.1 checked0650.2.2.1 checked0650.2.2.2
    (power_identity10 plusWeights0650) (power_identity10 minusWeights0650) g hg hmax

def envelope0650 : Envelope := ⟨coefficients0650, upper0650, bound0650⟩

def coefficients0651 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-25/1024), (-25/1024), (-225/16384), (-125/32768)]

def upper0651 : ℚ := (7077/2621440000000)

def plusWeights0651 : Fin 11 → ℚ := ![(7077/2621440000000), (7077/262144000000), (63693/524288000000), (21231/65536000000), (148617/262144000000), (445851/655360000000), (148617/262144000000), (21071/65536000000), (2389/20971520000), (25127/1310720000000), 0]

def minusWeights0651 : Fin 11 → ℚ := ![(7077/2621440000000), (7077/262144000000), (63693/524288000000), (21231/65536000000), (148617/262144000000), (445851/655360000000), (148617/262144000000), (21391/65536000000), (67661/524288000000), (45643/1310720000000), (7077/1310720000000)]

theorem checked0651 :
    (∀ i, 0 ≤ plusWeights0651 i) ∧
    (∀ i, 0 ≤ minusWeights0651 i) ∧
    (∀ i, plusCoefficients coefficients0651 upper0651 i = powerCoefficients10 plusWeights0651 i) ∧
    (∀ i, minusCoefficients coefficients0651 upper0651 i = powerCoefficients10 minusWeights0651 i) := by
  decide +kernel

theorem bound0651 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0651 g| ≤ (upper0651 : ℝ) :=
  abs_of_coefficients coefficients0651 upper0651 powerCoefficients10 plusWeights0651 minusWeights0651
    checked0651.1 checked0651.2.1 checked0651.2.2.1 checked0651.2.2.2
    (power_identity10 plusWeights0651) (power_identity10 minusWeights0651) g hg hmax

def envelope0651 : Envelope := ⟨coefficients0651, upper0651, bound0651⟩

def coefficients0652 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-3/128), (-13/512), (-339/8192), (-283/16384)]

def upper0652 : ℚ := (432663/163840000000000)

def plusWeights0652 : Fin 11 → ℚ := ![(432663/163840000000000), (432663/16384000000000), (3893967/32768000000000), (1297989/4096000000000), (9085923/16384000000000), (27257769/40960000000000), (9085923/16384000000000), (1288389/4096000000000), (3655247/32768000000000), (61693/3276800000000), 0]

def minusWeights0652 : Fin 11 → ℚ := ![(432663/163840000000000), (432663/16384000000000), (3893967/32768000000000), (1297989/4096000000000), (9085923/16384000000000), (27257769/40960000000000), (9085923/16384000000000), (1307589/4096000000000), (4132687/32768000000000), (556861/16384000000000), (432663/81920000000000)]

theorem checked0652 :
    (∀ i, 0 ≤ plusWeights0652 i) ∧
    (∀ i, 0 ≤ minusWeights0652 i) ∧
    (∀ i, plusCoefficients coefficients0652 upper0652 i = powerCoefficients10 plusWeights0652 i) ∧
    (∀ i, minusCoefficients coefficients0652 upper0652 i = powerCoefficients10 minusWeights0652 i) := by
  decide +kernel

theorem bound0652 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0652 g| ≤ (upper0652 : ℝ) :=
  abs_of_coefficients coefficients0652 upper0652 powerCoefficients10 plusWeights0652 minusWeights0652
    checked0652.1 checked0652.2.1 checked0652.2.2.1 checked0652.2.2.2
    (power_identity10 plusWeights0652) (power_identity10 minusWeights0652) g hg hmax

def envelope0652 : Envelope := ⟨coefficients0652, upper0652, bound0652⟩

def coefficients0653 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-47/2048), (-53/2048), (-171/8192), (-7/1024)]

def upper0653 : ℚ := (105483/40960000000000)

def plusWeights0653 : Fin 11 → ℚ := ![(105483/40960000000000), (105483/4096000000000), (949347/8192000000000), (316449/1024000000000), (2215143/4096000000000), (6645429/10240000000000), (2215143/4096000000000), (314099/1024000000000), (890827/8192000000000), (30031/1638400000000), 0]

def minusWeights0653 : Fin 11 → ℚ := ![(105483/40960000000000), (105483/4096000000000), (949347/8192000000000), (316449/1024000000000), (2215143/4096000000000), (6645429/10240000000000), (2215143/4096000000000), (318799/1024000000000), (1007867/8192000000000), (271777/8192000000000), (105483/20480000000000)]

theorem checked0653 :
    (∀ i, 0 ≤ plusWeights0653 i) ∧
    (∀ i, 0 ≤ minusWeights0653 i) ∧
    (∀ i, plusCoefficients coefficients0653 upper0653 i = powerCoefficients10 plusWeights0653 i) ∧
    (∀ i, minusCoefficients coefficients0653 upper0653 i = powerCoefficients10 minusWeights0653 i) := by
  decide +kernel

theorem bound0653 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0653 g| ≤ (upper0653 : ℝ) :=
  abs_of_coefficients coefficients0653 upper0653 powerCoefficients10 plusWeights0653 minusWeights0653
    checked0653.1 checked0653.2.1 checked0653.2.2.1 checked0653.2.2.2
    (power_identity10 plusWeights0653) (power_identity10 minusWeights0653) g hg hmax

def envelope0653 : Envelope := ⟨coefficients0653, upper0653, bound0653⟩

def coefficients0654 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-45/2048), (-55/2048), (-285/8192), (-55/4096)]

def upper0654 : ℚ := (1281/512000000000)

def plusWeights0654 : Fin 11 → ℚ := ![(1281/512000000000), (1281/51200000000), (11529/102400000000), (3843/12800000000), (26901/51200000000), (80703/128000000000), (26901/51200000000), (30519/102400000000), (21653/204800000000), (5851/327680000000), 0]

def minusWeights0654 : Fin 11 → ℚ := ![(1281/512000000000), (1281/51200000000), (11529/102400000000), (3843/12800000000), (26901/51200000000), (80703/128000000000), (26901/51200000000), (30969/102400000000), (24463/204800000000), (52729/1638400000000), (1281/256000000000)]

theorem checked0654 :
    (∀ i, 0 ≤ plusWeights0654 i) ∧
    (∀ i, 0 ≤ minusWeights0654 i) ∧
    (∀ i, plusCoefficients coefficients0654 upper0654 i = powerCoefficients10 plusWeights0654 i) ∧
    (∀ i, minusCoefficients coefficients0654 upper0654 i = powerCoefficients10 minusWeights0654 i) := by
  decide +kernel

theorem bound0654 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0654 g| ≤ (upper0654 : ℝ) :=
  abs_of_coefficients coefficients0654 upper0654 powerCoefficients10 plusWeights0654 minusWeights0654
    checked0654.1 checked0654.2.1 checked0654.2.2.1 checked0654.2.2.2
    (power_identity10 plusWeights0654) (power_identity10 minusWeights0654) g hg hmax

def envelope0654 : Envelope := ⟨coefficients0654, upper0654, bound0654⟩

def coefficients0655 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-45/2048), (-45/2048), (-1155/32768), (-975/65536)]

def upper0655 : ℚ := (64323/26214400000000)

def plusWeights0655 : Fin 11 → ℚ := ![(64323/26214400000000), (64323/2621440000000), (578907/5242880000000), (192969/655360000000), (1350783/2621440000000), (4052349/6553600000000), (1350783/2621440000000), (191529/655360000000), (108639/1048576000000), (228993/13107200000000), 0]

def minusWeights0655 : Fin 11 → ℚ := ![(64323/26214400000000), (64323/2621440000000), (578907/5242880000000), (192969/655360000000), (1350783/2621440000000), (4052349/6553600000000), (1350783/2621440000000), (194409/655360000000), (614619/5242880000000), (414237/13107200000000), (64323/13107200000000)]

theorem checked0655 :
    (∀ i, 0 ≤ plusWeights0655 i) ∧
    (∀ i, 0 ≤ minusWeights0655 i) ∧
    (∀ i, plusCoefficients coefficients0655 upper0655 i = powerCoefficients10 plusWeights0655 i) ∧
    (∀ i, minusCoefficients coefficients0655 upper0655 i = powerCoefficients10 minusWeights0655 i) := by
  decide +kernel

theorem bound0655 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0655 g| ≤ (upper0655 : ℝ) :=
  abs_of_coefficients coefficients0655 upper0655 powerCoefficients10 plusWeights0655 minusWeights0655
    checked0655.1 checked0655.2.1 checked0655.2.2.1 checked0655.2.2.2
    (power_identity10 plusWeights0655) (power_identity10 minusWeights0655) g hg hmax

def envelope0655 : Envelope := ⟨coefficients0655, upper0655, bound0655⟩

def coefficients0656 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-45/2048), (-45/2048), (-705/32768), (-525/65536)]

def upper0656 : ℚ := (12789/5242880000000)

def plusWeights0656 : Fin 11 → ℚ := ![(12789/5242880000000), (12789/524288000000), (115101/1048576000000), (38367/131072000000), (268569/524288000000), (805707/1310720000000), (268569/524288000000), (38079/131072000000), (539793/5242880000000), (227283/13107200000000), 0]

def minusWeights0656 : Fin 11 → ℚ := ![(12789/5242880000000), (12789/524288000000), (115101/1048576000000), (38367/131072000000), (268569/524288000000), (805707/1310720000000), (268569/524288000000), (7731/26214400000), (611217/5242880000000), (412167/13107200000000), (12789/2621440000000)]

theorem checked0656 :
    (∀ i, 0 ≤ plusWeights0656 i) ∧
    (∀ i, 0 ≤ minusWeights0656 i) ∧
    (∀ i, plusCoefficients coefficients0656 upper0656 i = powerCoefficients10 plusWeights0656 i) ∧
    (∀ i, minusCoefficients coefficients0656 upper0656 i = powerCoefficients10 minusWeights0656 i) := by
  decide +kernel

theorem bound0656 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0656 g| ≤ (upper0656 : ℝ) :=
  abs_of_coefficients coefficients0656 upper0656 powerCoefficients10 plusWeights0656 minusWeights0656
    checked0656.1 checked0656.2.1 checked0656.2.2.1 checked0656.2.2.2
    (power_identity10 plusWeights0656) (power_identity10 minusWeights0656) g hg hmax

def envelope0656 : Envelope := ⟨coefficients0656, upper0656, bound0656⟩

def coefficients0657 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-45/2048), (-45/2048), (-405/32768), (-225/65536)]

def upper0657 : ℚ := (63693/26214400000000)

def plusWeights0657 : Fin 11 → ℚ := ![(63693/26214400000000), (63693/2621440000000), (573237/5242880000000), (191079/655360000000), (1337553/2621440000000), (4012659/6553600000000), (1337553/2621440000000), (189639/655360000000), (21501/209715200000), (226143/13107200000000), 0]

def minusWeights0657 : Fin 11 → ℚ := ![(63693/26214400000000), (63693/2621440000000), (573237/5242880000000), (191079/655360000000), (1337553/2621440000000), (4012659/6553600000000), (1337553/2621440000000), (192519/655360000000), (608949/5242880000000), (410787/13107200000000), (63693/13107200000000)]

theorem checked0657 :
    (∀ i, 0 ≤ plusWeights0657 i) ∧
    (∀ i, 0 ≤ minusWeights0657 i) ∧
    (∀ i, plusCoefficients coefficients0657 upper0657 i = powerCoefficients10 plusWeights0657 i) ∧
    (∀ i, minusCoefficients coefficients0657 upper0657 i = powerCoefficients10 minusWeights0657 i) := by
  decide +kernel

theorem bound0657 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0657 g| ≤ (upper0657 : ℝ) :=
  abs_of_coefficients coefficients0657 upper0657 powerCoefficients10 plusWeights0657 minusWeights0657
    checked0657.1 checked0657.2.1 checked0657.2.2.1 checked0657.2.2.2
    (power_identity10 plusWeights0657) (power_identity10 minusWeights0657) g hg hmax

def envelope0657 : Envelope := ⟨coefficients0657, upper0657, bound0657⟩

def coefficients0658 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-37/2048), (-43/2048), (-447/16384), (-349/32768)]

def upper0658 : ℚ := (670089/327680000000000)

def plusWeights0658 : Fin 11 → ℚ := ![(670089/327680000000000), (670089/32768000000000), (6030801/65536000000000), (2010267/8192000000000), (14071869/32768000000000), (42215607/81920000000000), (14071869/32768000000000), (1995467/8192000000000), (5661841/65536000000000), (95567/6553600000000), 0]

def minusWeights0658 : Fin 11 → ℚ := ![(670089/327680000000000), (670089/32768000000000), (6030801/65536000000000), (2010267/8192000000000), (14071869/32768000000000), (42215607/81920000000000), (14071869/32768000000000), (2025067/8192000000000), (6399761/65536000000000), (862343/32768000000000), (670089/163840000000000)]

theorem checked0658 :
    (∀ i, 0 ≤ plusWeights0658 i) ∧
    (∀ i, 0 ≤ minusWeights0658 i) ∧
    (∀ i, plusCoefficients coefficients0658 upper0658 i = powerCoefficients10 plusWeights0658 i) ∧
    (∀ i, minusCoefficients coefficients0658 upper0658 i = powerCoefficients10 minusWeights0658 i) := by
  decide +kernel

theorem bound0658 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0658 g| ≤ (upper0658 : ℝ) :=
  abs_of_coefficients coefficients0658 upper0658 powerCoefficients10 plusWeights0658 minusWeights0658
    checked0658.1 checked0658.2.1 checked0658.2.2.1 checked0658.2.2.2
    (power_identity10 plusWeights0658) (power_identity10 minusWeights0658) g hg hmax

def envelope0658 : Envelope := ⟨coefficients0658, upper0658, bound0658⟩

def coefficients0659 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-37/2048), (-43/2048), (-297/16384), (-199/32768)]

def upper0659 : ℚ := (666939/327680000000000)

def plusWeights0659 : Fin 11 → ℚ := ![(666939/327680000000000), (666939/32768000000000), (6002451/65536000000000), (2000817/8192000000000), (14005719/32768000000000), (42017157/81920000000000), (14005719/32768000000000), (1986017/8192000000000), (5633491/65536000000000), (94997/6553600000000), 0]

def minusWeights0659 : Fin 11 → ℚ := ![(666939/327680000000000), (666939/32768000000000), (6002451/65536000000000), (2000817/8192000000000), (14005719/32768000000000), (42017157/81920000000000), (14005719/32768000000000), (2015617/8192000000000), (6371411/65536000000000), (858893/32768000000000), (666939/163840000000000)]

theorem checked0659 :
    (∀ i, 0 ≤ plusWeights0659 i) ∧
    (∀ i, 0 ≤ minusWeights0659 i) ∧
    (∀ i, plusCoefficients coefficients0659 upper0659 i = powerCoefficients10 plusWeights0659 i) ∧
    (∀ i, minusCoefficients coefficients0659 upper0659 i = powerCoefficients10 minusWeights0659 i) := by
  decide +kernel

theorem bound0659 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0659 g| ≤ (upper0659 : ℝ) :=
  abs_of_coefficients coefficients0659 upper0659 powerCoefficients10 plusWeights0659 minusWeights0659
    checked0659.1 checked0659.2.1 checked0659.2.2.1 checked0659.2.2.2
    (power_identity10 plusWeights0659) (power_identity10 minusWeights0659) g hg hmax

def envelope0659 : Envelope := ⟨coefficients0659, upper0659, bound0659⟩

def coefficients0660 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-135/8192), (45/4096), (-165/8192), (-375/32768)]

def upper0660 : ℚ := (20439/13107200000000)

def plusWeights0660 : Fin 11 → ℚ := ![(20439/13107200000000), (20439/1310720000000), (183951/2621440000000), (61317/327680000000), (429219/1310720000000), (1287657/3276800000000), (429219/1310720000000), (60777/327680000000), (171279/2621440000000), (71103/6553600000000), 0]

def minusWeights0660 : Fin 11 → ℚ := ![(20439/13107200000000), (20439/1310720000000), (183951/2621440000000), (61317/327680000000), (429219/1310720000000), (1287657/3276800000000), (429219/1310720000000), (61857/327680000000), (196623/2621440000000), (133287/6553600000000), (20439/6553600000000)]

theorem checked0660 :
    (∀ i, 0 ≤ plusWeights0660 i) ∧
    (∀ i, 0 ≤ minusWeights0660 i) ∧
    (∀ i, plusCoefficients coefficients0660 upper0660 i = powerCoefficients10 plusWeights0660 i) ∧
    (∀ i, minusCoefficients coefficients0660 upper0660 i = powerCoefficients10 minusWeights0660 i) := by
  decide +kernel

theorem bound0660 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0660 g| ≤ (upper0660 : ℝ) :=
  abs_of_coefficients coefficients0660 upper0660 powerCoefficients10 plusWeights0660 minusWeights0660
    checked0660.1 checked0660.2.1 checked0660.2.2.1 checked0660.2.2.2
    (power_identity10 plusWeights0660) (power_identity10 minusWeights0660) g hg hmax

def envelope0660 : Envelope := ⟨coefficients0660, upper0660, bound0660⟩

def coefficients0661 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-135/8192), (45/4096), (-45/4096), (-225/32768)]

def upper0661 : ℚ := (20313/13107200000000)

def plusWeights0661 : Fin 11 → ℚ := ![(20313/13107200000000), (20313/1310720000000), (182817/2621440000000), (60939/327680000000), (426573/1310720000000), (1279719/3276800000000), (426573/1310720000000), (60399/327680000000), (34029/524288000000), (70533/6553600000000), 0]

def minusWeights0661 : Fin 11 → ℚ := ![(20313/13107200000000), (20313/1310720000000), (182817/2621440000000), (60939/327680000000), (426573/1310720000000), (1279719/3276800000000), (426573/1310720000000), (61479/327680000000), (195489/2621440000000), (132597/6553600000000), (20313/6553600000000)]

theorem checked0661 :
    (∀ i, 0 ≤ plusWeights0661 i) ∧
    (∀ i, 0 ≤ minusWeights0661 i) ∧
    (∀ i, plusCoefficients coefficients0661 upper0661 i = powerCoefficients10 plusWeights0661 i) ∧
    (∀ i, minusCoefficients coefficients0661 upper0661 i = powerCoefficients10 minusWeights0661 i) := by
  decide +kernel

theorem bound0661 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0661 g| ≤ (upper0661 : ℝ) :=
  abs_of_coefficients coefficients0661 upper0661 powerCoefficients10 plusWeights0661 minusWeights0661
    checked0661.1 checked0661.2.1 checked0661.2.2.1 checked0661.2.2.2
    (power_identity10 plusWeights0661) (power_identity10 minusWeights0661) g hg hmax

def envelope0661 : Envelope := ⟨coefficients0661, upper0661, bound0661⟩

def coefficients0662 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/1024), (-15/1024), (-1695/32768), (-1575/65536)]

def upper0662 : ℚ := (43659/26214400000000)

def plusWeights0662 : Fin 11 → ℚ := ![(43659/26214400000000), (43659/2621440000000), (392931/5242880000000), (130977/655360000000), (916839/2621440000000), (2750517/6553600000000), (916839/2621440000000), (130017/655360000000), (369123/5242880000000), (156177/13107200000000), 0]

def minusWeights0662 : Fin 11 → ℚ := ![(43659/26214400000000), (43659/2621440000000), (392931/5242880000000), (130977/655360000000), (916839/2621440000000), (2750517/6553600000000), (916839/2621440000000), (131937/655360000000), (416739/5242880000000), (280413/13107200000000), (43659/13107200000000)]

theorem checked0662 :
    (∀ i, 0 ≤ plusWeights0662 i) ∧
    (∀ i, 0 ≤ minusWeights0662 i) ∧
    (∀ i, plusCoefficients coefficients0662 upper0662 i = powerCoefficients10 plusWeights0662 i) ∧
    (∀ i, minusCoefficients coefficients0662 upper0662 i = powerCoefficients10 minusWeights0662 i) := by
  decide +kernel

theorem bound0662 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0662 g| ≤ (upper0662 : ℝ) :=
  abs_of_coefficients coefficients0662 upper0662 powerCoefficients10 plusWeights0662 minusWeights0662
    checked0662.1 checked0662.2.1 checked0662.2.2.1 checked0662.2.2.2
    (power_identity10 plusWeights0662) (power_identity10 minusWeights0662) g hg hmax

def envelope0662 : Envelope := ⟨coefficients0662, upper0662, bound0662⟩

def coefficients0663 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/1024), (-15/1024), (-255/8192), (-225/16384)]

def upper0663 : ℚ := (10773/6553600000000)

def plusWeights0663 : Fin 11 → ℚ := ![(10773/6553600000000), (10773/655360000000), (96957/1310720000000), (32319/163840000000), (226233/655360000000), (678699/1638400000000), (226233/655360000000), (32079/163840000000), (18201/262144000000), (38403/3276800000000), 0]

def minusWeights0663 : Fin 11 → ℚ := ![(10773/6553600000000), (10773/655360000000), (96957/1310720000000), (32319/163840000000), (226233/655360000000), (678699/1638400000000), (226233/655360000000), (32559/163840000000), (102909/1310720000000), (69327/3276800000000), (10773/3276800000000)]

theorem checked0663 :
    (∀ i, 0 ≤ plusWeights0663 i) ∧
    (∀ i, 0 ≤ minusWeights0663 i) ∧
    (∀ i, plusCoefficients coefficients0663 upper0663 i = powerCoefficients10 plusWeights0663 i) ∧
    (∀ i, minusCoefficients coefficients0663 upper0663 i = powerCoefficients10 minusWeights0663 i) := by
  decide +kernel

theorem bound0663 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0663 g| ≤ (upper0663 : ℝ) :=
  abs_of_coefficients coefficients0663 upper0663 powerCoefficients10 plusWeights0663 minusWeights0663
    checked0663.1 checked0663.2.1 checked0663.2.2.1 checked0663.2.2.2
    (power_identity10 plusWeights0663) (power_identity10 minusWeights0663) g hg hmax

def envelope0663 : Envelope := ⟨coefficients0663, upper0663, bound0663⟩

def coefficients0664 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/1024), (-15/1024), (-285/16384), (-225/32768)]

def upper0664 : ℚ := (21357/13107200000000)

def plusWeights0664 : Fin 11 → ℚ := ![(21357/13107200000000), (21357/1310720000000), (192213/2621440000000), (64071/327680000000), (448497/1310720000000), (1345491/3276800000000), (448497/1310720000000), (63591/327680000000), (180309/2621440000000), (75951/6553600000000), 0]

def minusWeights0664 : Fin 11 → ℚ := ![(21357/13107200000000), (21357/1310720000000), (192213/2621440000000), (64071/327680000000), (448497/1310720000000), (1345491/3276800000000), (448497/1310720000000), (64551/327680000000), (204117/2621440000000), (137619/6553600000000), (21357/6553600000000)]

theorem checked0664 :
    (∀ i, 0 ≤ plusWeights0664 i) ∧
    (∀ i, 0 ≤ minusWeights0664 i) ∧
    (∀ i, plusCoefficients coefficients0664 upper0664 i = powerCoefficients10 plusWeights0664 i) ∧
    (∀ i, minusCoefficients coefficients0664 upper0664 i = powerCoefficients10 minusWeights0664 i) := by
  decide +kernel

theorem bound0664 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0664 g| ≤ (upper0664 : ℝ) :=
  abs_of_coefficients coefficients0664 upper0664 powerCoefficients10 plusWeights0664 minusWeights0664
    checked0664.1 checked0664.2.1 checked0664.2.2.1 checked0664.2.2.2
    (power_identity10 plusWeights0664) (power_identity10 minusWeights0664) g hg hmax

def envelope0664 : Envelope := ⟨coefficients0664, upper0664, bound0664⟩

def coefficients0665 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-57/4096), (-63/4096), (-537/32768), (-399/65536)]

def upper0665 : ℚ := (1023939/655360000000000)

def plusWeights0665 : Fin 11 → ℚ := ![(1023939/655360000000000), (1023939/65536000000000), (9215451/131072000000000), (3071817/16384000000000), (21502719/65536000000000), (64508157/163840000000000), (21502719/65536000000000), (3049017/16384000000000), (8648091/131072000000000), (145821/13107200000000), 0]

def minusWeights0665 : Fin 11 → ℚ := ![(1023939/655360000000000), (1023939/65536000000000), (9215451/131072000000000), (3071817/16384000000000), (21502719/65536000000000), (64508157/163840000000000), (21502719/65536000000000), (3094617/16384000000000), (9782811/131072000000000), (1318773/65536000000000), (1023939/327680000000000)]

theorem checked0665 :
    (∀ i, 0 ≤ plusWeights0665 i) ∧
    (∀ i, 0 ≤ minusWeights0665 i) ∧
    (∀ i, plusCoefficients coefficients0665 upper0665 i = powerCoefficients10 plusWeights0665 i) ∧
    (∀ i, minusCoefficients coefficients0665 upper0665 i = powerCoefficients10 minusWeights0665 i) := by
  decide +kernel

theorem bound0665 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0665 g| ≤ (upper0665 : ℝ) :=
  abs_of_coefficients coefficients0665 upper0665 powerCoefficients10 plusWeights0665 minusWeights0665
    checked0665.1 checked0665.2.1 checked0665.2.2.1 checked0665.2.2.2
    (power_identity10 plusWeights0665) (power_identity10 minusWeights0665) g hg hmax

def envelope0665 : Envelope := ⟨coefficients0665, upper0665, bound0665⟩

def coefficients0666 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-1929/32768), (-1773/65536)]

def upper0666 : ℚ := (1009953/655360000000000)

def plusWeights0666 : Fin 11 → ℚ := ![(1009953/655360000000000), (1009953/65536000000000), (9089577/131072000000000), (3029859/16384000000000), (21209013/65536000000000), (63627039/163840000000000), (21209013/65536000000000), (3008259/16384000000000), (8550057/131072000000000), (29031/2621440000000), 0]

def minusWeights0666 : Fin 11 → ℚ := ![(1009953/655360000000000), (1009953/65536000000000), (9089577/131072000000000), (3029859/16384000000000), (21209013/65536000000000), (63627039/163840000000000), (21209013/65536000000000), (3051459/16384000000000), (9629097/131072000000000), (1294131/65536000000000), (1009953/327680000000000)]

theorem checked0666 :
    (∀ i, 0 ≤ plusWeights0666 i) ∧
    (∀ i, 0 ≤ minusWeights0666 i) ∧
    (∀ i, plusCoefficients coefficients0666 upper0666 i = powerCoefficients10 plusWeights0666 i) ∧
    (∀ i, minusCoefficients coefficients0666 upper0666 i = powerCoefficients10 minusWeights0666 i) := by
  decide +kernel

theorem bound0666 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0666 g| ≤ (upper0666 : ℝ) :=
  abs_of_coefficients coefficients0666 upper0666 powerCoefficients10 plusWeights0666 minusWeights0666
    checked0666.1 checked0666.2.1 checked0666.2.2.1 checked0666.2.2.2
    (power_identity10 plusWeights0666) (power_identity10 minusWeights0666) g hg hmax

def envelope0666 : Envelope := ⟨coefficients0666, upper0666, bound0666⟩

def coefficients0667 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-1629/32768), (-1473/65536)]

def upper0667 : ℚ := (1003653/655360000000000)

def plusWeights0667 : Fin 11 → ℚ := ![(1003653/655360000000000), (1003653/65536000000000), (9032877/131072000000000), (3010959/16384000000000), (21076713/65536000000000), (63230139/163840000000000), (21076713/65536000000000), (2989359/16384000000000), (8493357/131072000000000), (28803/2621440000000), 0]

def minusWeights0667 : Fin 11 → ℚ := ![(1003653/655360000000000), (1003653/65536000000000), (9032877/131072000000000), (3010959/16384000000000), (21076713/65536000000000), (63230139/163840000000000), (21076713/65536000000000), (3032559/16384000000000), (9572397/131072000000000), (1287231/65536000000000), (1003653/327680000000000)]

theorem checked0667 :
    (∀ i, 0 ≤ plusWeights0667 i) ∧
    (∀ i, 0 ≤ minusWeights0667 i) ∧
    (∀ i, plusCoefficients coefficients0667 upper0667 i = powerCoefficients10 plusWeights0667 i) ∧
    (∀ i, minusCoefficients coefficients0667 upper0667 i = powerCoefficients10 minusWeights0667 i) := by
  decide +kernel

theorem bound0667 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0667 g| ≤ (upper0667 : ℝ) :=
  abs_of_coefficients coefficients0667 upper0667 powerCoefficients10 plusWeights0667 minusWeights0667
    checked0667.1 checked0667.2.1 checked0667.2.2.1 checked0667.2.2.2
    (power_identity10 plusWeights0667) (power_identity10 minusWeights0667) g hg hmax

def envelope0667 : Envelope := ⟨coefficients0667, upper0667, bound0667⟩

def coefficients0668 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-69/2048), (-237/16384)]

def upper0668 : ℚ := (248157/163840000000000)

def plusWeights0668 : Fin 11 → ℚ := ![(248157/163840000000000), (248157/16384000000000), (2233413/32768000000000), (744471/4096000000000), (5211297/16384000000000), (15633891/40960000000000), (5211297/16384000000000), (739071/4096000000000), (2098533/32768000000000), (7101/655360000000), 0]

def minusWeights0668 : Fin 11 → ℚ := ![(248157/163840000000000), (248157/16384000000000), (2233413/32768000000000), (744471/4096000000000), (5211297/16384000000000), (15633891/40960000000000), (5211297/16384000000000), (749871/4096000000000), (2368293/32768000000000), (318789/16384000000000), (248157/81920000000000)]

theorem checked0668 :
    (∀ i, 0 ≤ plusWeights0668 i) ∧
    (∀ i, 0 ≤ minusWeights0668 i) ∧
    (∀ i, plusCoefficients coefficients0668 upper0668 i = powerCoefficients10 plusWeights0668 i) ∧
    (∀ i, minusCoefficients coefficients0668 upper0668 i = powerCoefficients10 minusWeights0668 i) := by
  decide +kernel

theorem bound0668 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0668 g| ≤ (upper0668 : ℝ) :=
  abs_of_coefficients coefficients0668 upper0668 powerCoefficients10 plusWeights0668 minusWeights0668
    checked0668.1 checked0668.2.1 checked0668.2.2.1 checked0668.2.2.2
    (power_identity10 plusWeights0668) (power_identity10 minusWeights0668) g hg hmax

def envelope0668 : Envelope := ⟨coefficients0668, upper0668, bound0668⟩

def coefficients0669 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-113/4096), (-187/16384)]

def upper0669 : ℚ := (247107/163840000000000)

def plusWeights0669 : Fin 11 → ℚ := ![(247107/163840000000000), (247107/16384000000000), (2223963/32768000000000), (741321/4096000000000), (5189247/16384000000000), (15567741/40960000000000), (5189247/16384000000000), (735921/4096000000000), (2089083/32768000000000), (7063/655360000000), 0]

def minusWeights0669 : Fin 11 → ℚ := ![(247107/163840000000000), (247107/16384000000000), (2223963/32768000000000), (741321/4096000000000), (5189247/16384000000000), (15567741/40960000000000), (5189247/16384000000000), (746721/4096000000000), (2358843/32768000000000), (317639/16384000000000), (247107/81920000000000)]

theorem checked0669 :
    (∀ i, 0 ≤ plusWeights0669 i) ∧
    (∀ i, 0 ≤ minusWeights0669 i) ∧
    (∀ i, plusCoefficients coefficients0669 upper0669 i = powerCoefficients10 plusWeights0669 i) ∧
    (∀ i, minusCoefficients coefficients0669 upper0669 i = powerCoefficients10 minusWeights0669 i) := by
  decide +kernel

theorem bound0669 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0669 g| ≤ (upper0669 : ℝ) :=
  abs_of_coefficients coefficients0669 upper0669 powerCoefficients10 plusWeights0669 minusWeights0669
    checked0669.1 checked0669.2.1 checked0669.2.2.1 checked0669.2.2.2
    (power_identity10 plusWeights0669) (power_identity10 minusWeights0669) g hg hmax

def envelope0669 : Envelope := ⟨coefficients0669, upper0669, bound0669⟩

def coefficients0670 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-151/8192), (-7/1024)]

def upper0670 : ℚ := (61383/40960000000000)

def plusWeights0670 : Fin 11 → ℚ := ![(61383/40960000000000), (61383/4096000000000), (552447/8192000000000), (184149/1024000000000), (1289043/4096000000000), (3867129/10240000000000), (1289043/4096000000000), (182799/1024000000000), (518727/8192000000000), (3503/327680000000), 0]

def minusWeights0670 : Fin 11 → ℚ := ![(61383/40960000000000), (61383/4096000000000), (552447/8192000000000), (184149/1024000000000), (1289043/4096000000000), (3867129/10240000000000), (1289043/4096000000000), (185499/1024000000000), (586167/8192000000000), (157957/8192000000000), (61383/20480000000000)]

theorem checked0670 :
    (∀ i, 0 ≤ plusWeights0670 i) ∧
    (∀ i, 0 ≤ minusWeights0670 i) ∧
    (∀ i, plusCoefficients coefficients0670 upper0670 i = powerCoefficients10 plusWeights0670 i) ∧
    (∀ i, minusCoefficients coefficients0670 upper0670 i = powerCoefficients10 minusWeights0670 i) := by
  decide +kernel

theorem bound0670 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0670 g| ≤ (upper0670 : ℝ) :=
  abs_of_coefficients coefficients0670 upper0670 powerCoefficients10 plusWeights0670 minusWeights0670
    checked0670.1 checked0670.2.1 checked0670.2.2.1 checked0670.2.2.2
    (power_identity10 plusWeights0670) (power_identity10 minusWeights0670) g hg hmax

def envelope0670 : Envelope := ⟨coefficients0670, upper0670, bound0670⟩

def coefficients0671 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/2048), (-33/2048), (-63/4096), (-87/16384)]

def upper0671 : ℚ := (245007/163840000000000)

def plusWeights0671 : Fin 11 → ℚ := ![(245007/163840000000000), (245007/16384000000000), (2205063/32768000000000), (735021/4096000000000), (5145147/16384000000000), (15435441/40960000000000), (5145147/16384000000000), (729621/4096000000000), (2070183/32768000000000), (6987/655360000000), 0]

def minusWeights0671 : Fin 11 → ℚ := ![(245007/163840000000000), (245007/16384000000000), (2205063/32768000000000), (735021/4096000000000), (5145147/16384000000000), (15435441/40960000000000), (5145147/16384000000000), (740421/4096000000000), (2339943/32768000000000), (315339/16384000000000), (245007/81920000000000)]

theorem checked0671 :
    (∀ i, 0 ≤ plusWeights0671 i) ∧
    (∀ i, 0 ≤ minusWeights0671 i) ∧
    (∀ i, plusCoefficients coefficients0671 upper0671 i = powerCoefficients10 plusWeights0671 i) ∧
    (∀ i, minusCoefficients coefficients0671 upper0671 i = powerCoefficients10 minusWeights0671 i) := by
  decide +kernel

theorem bound0671 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0671 g| ≤ (upper0671 : ℝ) :=
  abs_of_coefficients coefficients0671 upper0671 powerCoefficients10 plusWeights0671 minusWeights0671
    checked0671.1 checked0671.2.1 checked0671.2.2.1 checked0671.2.2.2
    (power_identity10 plusWeights0671) (power_identity10 minusWeights0671) g hg hmax

def envelope0671 : Envelope := ⟨coefficients0671, upper0671, bound0671⟩

end BilayerDressed.CubicQuarticEnvelopes

import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0768 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (285/16384), (345/32768), (1245/131072)]

def upper0768 : ℚ := (48609/262144000000000)

def plusWeights0768 : Fin 11 → ℚ := ![(48609/262144000000000), (48609/26214400000000), (437481/52428800000000), (145827/6553600000000), (1020789/26214400000000), (3062367/65536000000000), (1020789/26214400000000), (145827/6553600000000), (446601/52428800000000), (11601/5242880000000), (48609/131072000000000)]

def minusWeights0768 : Fin 11 → ℚ := ![(48609/262144000000000), (48609/26214400000000), (437481/52428800000000), (145827/6553600000000), (1020789/26214400000000), (3062367/65536000000000), (1020789/26214400000000), (145827/6553600000000), (428361/52428800000000), (39213/26214400000000), 0]

theorem checked0768 :
    (∀ i, 0 ≤ plusWeights0768 i) ∧
    (∀ i, 0 ≤ minusWeights0768 i) ∧
    (∀ i, plusCoefficients coefficients0768 upper0768 i = powerCoefficients10 plusWeights0768 i) ∧
    (∀ i, minusCoefficients coefficients0768 upper0768 i = powerCoefficients10 minusWeights0768 i) := by
  decide +kernel

theorem bound0768 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0768 g| ≤ (upper0768 : ℝ) :=
  abs_of_coefficients coefficients0768 upper0768 powerCoefficients10 plusWeights0768 minusWeights0768
    checked0768.1 checked0768.2.1 checked0768.2.2.1 checked0768.2.2.2
    (power_identity10 plusWeights0768) (power_identity10 minusWeights0768) g hg hmax

def envelope0768 : Envelope := ⟨coefficients0768, upper0768, bound0768⟩

def coefficients0769 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (585/32768), (645/65536), (2745/262144)]

def upper0769 : ℚ := (99309/524288000000000)

def plusWeights0769 : Fin 11 → ℚ := ![(99309/524288000000000), (99309/52428800000000), (893781/104857600000000), (297927/13107200000000), (2085489/52428800000000), (6256467/131072000000000), (2085489/52428800000000), (297927/13107200000000), (912501/104857600000000), (23709/10485760000000), (99309/262144000000000)]

def minusWeights0769 : Fin 11 → ℚ := ![(99309/524288000000000), (99309/52428800000000), (893781/104857600000000), (297927/13107200000000), (2085489/52428800000000), (6256467/131072000000000), (2085489/52428800000000), (297927/13107200000000), (875061/104857600000000), (80073/52428800000000), 0]

theorem checked0769 :
    (∀ i, 0 ≤ plusWeights0769 i) ∧
    (∀ i, 0 ≤ minusWeights0769 i) ∧
    (∀ i, plusCoefficients coefficients0769 upper0769 i = powerCoefficients10 plusWeights0769 i) ∧
    (∀ i, minusCoefficients coefficients0769 upper0769 i = powerCoefficients10 minusWeights0769 i) := by
  decide +kernel

theorem bound0769 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0769 g| ≤ (upper0769 : ℝ) :=
  abs_of_coefficients coefficients0769 upper0769 powerCoefficients10 plusWeights0769 minusWeights0769
    checked0769.1 checked0769.2.1 checked0769.2.2.1 checked0769.2.2.2
    (power_identity10 plusWeights0769) (power_identity10 minusWeights0769) g hg hmax

def envelope0769 : Envelope := ⟨coefficients0769, upper0769, bound0769⟩

def coefficients0770 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (705/32768), (885/65536), (2805/131072)]

def upper0770 : ℚ := (60501/262144000000000)

def plusWeights0770 : Fin 11 → ℚ := ![(60501/262144000000000), (60501/26214400000000), (544509/52428800000000), (181503/6553600000000), (1270521/26214400000000), (3811563/65536000000000), (1270521/26214400000000), (181503/6553600000000), (555789/52428800000000), (14427/5242880000000), (60501/131072000000000)]

def minusWeights0770 : Fin 11 → ℚ := ![(60501/262144000000000), (60501/26214400000000), (544509/52428800000000), (181503/6553600000000), (1270521/26214400000000), (3811563/65536000000000), (1270521/26214400000000), (181503/6553600000000), (533229/52428800000000), (48867/26214400000000), 0]

theorem checked0770 :
    (∀ i, 0 ≤ plusWeights0770 i) ∧
    (∀ i, 0 ≤ minusWeights0770 i) ∧
    (∀ i, plusCoefficients coefficients0770 upper0770 i = powerCoefficients10 plusWeights0770 i) ∧
    (∀ i, minusCoefficients coefficients0770 upper0770 i = powerCoefficients10 minusWeights0770 i) := by
  decide +kernel

theorem bound0770 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0770 g| ≤ (upper0770 : ℝ) :=
  abs_of_coefficients coefficients0770 upper0770 powerCoefficients10 plusWeights0770 minusWeights0770
    checked0770.1 checked0770.2.1 checked0770.2.2.1 checked0770.2.2.2
    (power_identity10 plusWeights0770) (power_identity10 minusWeights0770) g hg hmax

def envelope0770 : Envelope := ⟨coefficients0770, upper0770, bound0770⟩

def coefficients0771 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (375/16384), (375/32768), (1875/262144)]

def upper0771 : ℚ := (1011/4194304000000)

def plusWeights0771 : Fin 11 → ℚ := ![(1011/4194304000000), (1011/419430400000), (9099/838860800000), (3033/104857600000), (21231/419430400000), (63693/1048576000000), (21231/419430400000), (3033/104857600000), (9291/838860800000), (6039/2097152000000), (1011/2097152000000)]

def minusWeights0771 : Fin 11 → ℚ := ![(1011/4194304000000), (1011/419430400000), (9099/838860800000), (3033/104857600000), (21231/419430400000), (63693/1048576000000), (21231/419430400000), (3033/104857600000), (8907/838860800000), (4071/2097152000000), 0]

theorem checked0771 :
    (∀ i, 0 ≤ plusWeights0771 i) ∧
    (∀ i, 0 ≤ minusWeights0771 i) ∧
    (∀ i, plusCoefficients coefficients0771 upper0771 i = powerCoefficients10 plusWeights0771 i) ∧
    (∀ i, minusCoefficients coefficients0771 upper0771 i = powerCoefficients10 minusWeights0771 i) := by
  decide +kernel

theorem bound0771 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0771 g| ≤ (upper0771 : ℝ) :=
  abs_of_coefficients coefficients0771 upper0771 powerCoefficients10 plusWeights0771 minusWeights0771
    checked0771.1 checked0771.2.1 checked0771.2.2.1 checked0771.2.2.2
    (power_identity10 plusWeights0771) (power_identity10 minusWeights0771) g hg hmax

def envelope0771 : Envelope := ⟨coefficients0771, upper0771, bound0771⟩

def coefficients0772 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/16384), (585/32768), (1305/65536)]

def upper0772 : ℚ := (35001/131072000000000)

def plusWeights0772 : Fin 11 → ℚ := ![(35001/131072000000000), (35001/13107200000000), (315009/26214400000000), (105003/3276800000000), (735021/13107200000000), (2205063/32768000000000), (735021/13107200000000), (105003/3276800000000), (321489/26214400000000), (8343/2621440000000), (35001/65536000000000)]

def minusWeights0772 : Fin 11 → ℚ := ![(35001/131072000000000), (35001/13107200000000), (315009/26214400000000), (105003/3276800000000), (735021/13107200000000), (2205063/32768000000000), (735021/13107200000000), (105003/3276800000000), (308529/26214400000000), (28287/13107200000000), 0]

theorem checked0772 :
    (∀ i, 0 ≤ plusWeights0772 i) ∧
    (∀ i, 0 ≤ minusWeights0772 i) ∧
    (∀ i, plusCoefficients coefficients0772 upper0772 i = powerCoefficients10 plusWeights0772 i) ∧
    (∀ i, minusCoefficients coefficients0772 upper0772 i = powerCoefficients10 minusWeights0772 i) := by
  decide +kernel

theorem bound0772 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0772 g| ≤ (upper0772 : ℝ) :=
  abs_of_coefficients coefficients0772 upper0772 powerCoefficients10 plusWeights0772 minusWeights0772
    checked0772.1 checked0772.2.1 checked0772.2.2.1 checked0772.2.2.2
    (power_identity10 plusWeights0772) (power_identity10 minusWeights0772) g hg hmax

def envelope0772 : Envelope := ⟨coefficients0772, upper0772, bound0772⟩

def coefficients0773 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/16384), (585/32768), (2985/131072)]

def upper0773 : ℚ := (70077/262144000000000)

def plusWeights0773 : Fin 11 → ℚ := ![(70077/262144000000000), (70077/26214400000000), (630693/52428800000000), (210231/6553600000000), (1471617/26214400000000), (4414851/65536000000000), (1471617/26214400000000), (210231/6553600000000), (643653/52428800000000), (16701/5242880000000), (70077/131072000000000)]

def minusWeights0773 : Fin 11 → ℚ := ![(70077/262144000000000), (70077/26214400000000), (630693/52428800000000), (210231/6553600000000), (1471617/26214400000000), (4414851/65536000000000), (1471617/26214400000000), (210231/6553600000000), (617733/52428800000000), (56649/26214400000000), 0]

theorem checked0773 :
    (∀ i, 0 ≤ plusWeights0773 i) ∧
    (∀ i, 0 ≤ minusWeights0773 i) ∧
    (∀ i, plusCoefficients coefficients0773 upper0773 i = powerCoefficients10 plusWeights0773 i) ∧
    (∀ i, minusCoefficients coefficients0773 upper0773 i = powerCoefficients10 minusWeights0773 i) := by
  decide +kernel

theorem bound0773 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0773 g| ≤ (upper0773 : ℝ) :=
  abs_of_coefficients coefficients0773 upper0773 powerCoefficients10 plusWeights0773 minusWeights0773
    checked0773.1 checked0773.2.1 checked0773.2.2.1 checked0773.2.2.2
    (power_identity10 plusWeights0773) (power_identity10 minusWeights0773) g hg hmax

def envelope0773 : Envelope := ⟨coefficients0773, upper0773, bound0773⟩

def coefficients0774 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/16384), (585/32768), (6345/262144)]

def upper0774 : ℚ := (140229/524288000000000)

def plusWeights0774 : Fin 11 → ℚ := ![(140229/524288000000000), (140229/52428800000000), (1262061/104857600000000), (420687/13107200000000), (2944809/52428800000000), (8834427/131072000000000), (2944809/52428800000000), (420687/13107200000000), (1287981/104857600000000), (33417/10485760000000), (140229/262144000000000)]

def minusWeights0774 : Fin 11 → ℚ := ![(140229/524288000000000), (140229/52428800000000), (1262061/104857600000000), (420687/13107200000000), (2944809/52428800000000), (8834427/131072000000000), (2944809/52428800000000), (420687/13107200000000), (1236141/104857600000000), (113373/52428800000000), 0]

theorem checked0774 :
    (∀ i, 0 ≤ plusWeights0774 i) ∧
    (∀ i, 0 ≤ minusWeights0774 i) ∧
    (∀ i, plusCoefficients coefficients0774 upper0774 i = powerCoefficients10 plusWeights0774 i) ∧
    (∀ i, minusCoefficients coefficients0774 upper0774 i = powerCoefficients10 minusWeights0774 i) := by
  decide +kernel

theorem bound0774 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0774 g| ≤ (upper0774 : ℝ) :=
  abs_of_coefficients coefficients0774 upper0774 powerCoefficients10 plusWeights0774 minusWeights0774
    checked0774.1 checked0774.2.1 checked0774.2.2.1 checked0774.2.2.2
    (power_identity10 plusWeights0774) (power_identity10 minusWeights0774) g hg hmax

def envelope0774 : Envelope := ⟨coefficients0774, upper0774, bound0774⟩

def coefficients0775 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/16384), (585/32768), (5985/131072)]

def upper0775 : ℚ := (70677/262144000000000)

def plusWeights0775 : Fin 11 → ℚ := ![(70677/262144000000000), (70677/26214400000000), (636093/52428800000000), (212031/6553600000000), (1484217/26214400000000), (4452651/65536000000000), (1484217/26214400000000), (212031/6553600000000), (649053/52428800000000), (16821/5242880000000), (70677/131072000000000)]

def minusWeights0775 : Fin 11 → ℚ := ![(70677/262144000000000), (70677/26214400000000), (636093/52428800000000), (212031/6553600000000), (1484217/26214400000000), (4452651/65536000000000), (1484217/26214400000000), (212031/6553600000000), (623133/52428800000000), (57249/26214400000000), 0]

theorem checked0775 :
    (∀ i, 0 ≤ plusWeights0775 i) ∧
    (∀ i, 0 ≤ minusWeights0775 i) ∧
    (∀ i, plusCoefficients coefficients0775 upper0775 i = powerCoefficients10 plusWeights0775 i) ∧
    (∀ i, minusCoefficients coefficients0775 upper0775 i = powerCoefficients10 minusWeights0775 i) := by
  decide +kernel

theorem bound0775 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0775 g| ≤ (upper0775 : ℝ) :=
  abs_of_coefficients coefficients0775 upper0775 powerCoefficients10 plusWeights0775 minusWeights0775
    checked0775.1 checked0775.2.1 checked0775.2.2.1 checked0775.2.2.2
    (power_identity10 plusWeights0775) (power_identity10 minusWeights0775) g hg hmax

def envelope0775 : Envelope := ⟨coefficients0775, upper0775, bound0775⟩

def coefficients0776 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (105/4096), (105/4096), (105/16384)]

def upper0776 : ℚ := (9261/32768000000000)

def plusWeights0776 : Fin 11 → ℚ := ![(9261/32768000000000), (9261/3276800000000), (83349/6553600000000), (27783/819200000000), (194481/3276800000000), (583443/8192000000000), (194481/3276800000000), (27783/819200000000), (85029/6553600000000), (441/131072000000), (9261/16384000000000)]

def minusWeights0776 : Fin 11 → ℚ := ![(9261/32768000000000), (9261/3276800000000), (83349/6553600000000), (27783/819200000000), (194481/3276800000000), (583443/8192000000000), (194481/3276800000000), (27783/819200000000), (81669/6553600000000), (7497/3276800000000), 0]

theorem checked0776 :
    (∀ i, 0 ≤ plusWeights0776 i) ∧
    (∀ i, 0 ≤ minusWeights0776 i) ∧
    (∀ i, plusCoefficients coefficients0776 upper0776 i = powerCoefficients10 plusWeights0776 i) ∧
    (∀ i, minusCoefficients coefficients0776 upper0776 i = powerCoefficients10 minusWeights0776 i) := by
  decide +kernel

theorem bound0776 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0776 g| ≤ (upper0776 : ℝ) :=
  abs_of_coefficients coefficients0776 upper0776 powerCoefficients10 plusWeights0776 minusWeights0776
    checked0776.1 checked0776.2.1 checked0776.2.2.1 checked0776.2.2.2
    (power_identity10 plusWeights0776) (power_identity10 minusWeights0776) g hg hmax

def envelope0776 : Envelope := ⟨coefficients0776, upper0776, bound0776⟩

def coefficients0777 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (225/8192), (325/16384), (725/32768)]

def upper0777 : ℚ := (3889/13107200000000)

def plusWeights0777 : Fin 11 → ℚ := ![(3889/13107200000000), (3889/1310720000000), (35001/2621440000000), (11667/327680000000), (81669/1310720000000), (245007/3276800000000), (81669/1310720000000), (11667/327680000000), (35721/2621440000000), (927/262144000000), (3889/6553600000000)]

def minusWeights0777 : Fin 11 → ℚ := ![(3889/13107200000000), (3889/1310720000000), (35001/2621440000000), (11667/327680000000), (81669/1310720000000), (245007/3276800000000), (81669/1310720000000), (11667/327680000000), (34281/2621440000000), (3143/1310720000000), 0]

theorem checked0777 :
    (∀ i, 0 ≤ plusWeights0777 i) ∧
    (∀ i, 0 ≤ minusWeights0777 i) ∧
    (∀ i, plusCoefficients coefficients0777 upper0777 i = powerCoefficients10 plusWeights0777 i) ∧
    (∀ i, minusCoefficients coefficients0777 upper0777 i = powerCoefficients10 minusWeights0777 i) := by
  decide +kernel

theorem bound0777 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0777 g| ≤ (upper0777 : ℝ) :=
  abs_of_coefficients coefficients0777 upper0777 powerCoefficients10 plusWeights0777 minusWeights0777
    checked0777.1 checked0777.2.1 checked0777.2.2.1 checked0777.2.2.2
    (power_identity10 plusWeights0777) (power_identity10 minusWeights0777) g hg hmax

def envelope0777 : Envelope := ⟨coefficients0777, upper0777, bound0777⟩

def coefficients0778 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (945/32768), (1365/65536), (855/32768)]

def upper0778 : ℚ := (5109/16384000000000)

def plusWeights0778 : Fin 11 → ℚ := ![(5109/16384000000000), (5109/1638400000000), (45981/3276800000000), (15327/409600000000), (107289/1638400000000), (321867/4096000000000), (107289/1638400000000), (15327/409600000000), (23463/1638400000000), (9741/2621440000000), (5109/8192000000000)]

def minusWeights0778 : Fin 11 → ℚ := ![(5109/16384000000000), (5109/1638400000000), (45981/3276800000000), (15327/409600000000), (107289/1638400000000), (321867/4096000000000), (107289/1638400000000), (15327/409600000000), (11259/819200000000), (33039/13107200000000), 0]

theorem checked0778 :
    (∀ i, 0 ≤ plusWeights0778 i) ∧
    (∀ i, 0 ≤ minusWeights0778 i) ∧
    (∀ i, plusCoefficients coefficients0778 upper0778 i = powerCoefficients10 plusWeights0778 i) ∧
    (∀ i, minusCoefficients coefficients0778 upper0778 i = powerCoefficients10 minusWeights0778 i) := by
  decide +kernel

theorem bound0778 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0778 g| ≤ (upper0778 : ℝ) :=
  abs_of_coefficients coefficients0778 upper0778 powerCoefficients10 plusWeights0778 minusWeights0778
    checked0778.1 checked0778.2.1 checked0778.2.2.1 checked0778.2.2.2
    (power_identity10 plusWeights0778) (power_identity10 minusWeights0778) g hg hmax

def envelope0778 : Envelope := ⟨coefficients0778, upper0778, bound0778⟩

def coefficients0779 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/4096), (195/8192), (435/16384)]

def upper0779 : ℚ := (11667/32768000000000)

def plusWeights0779 : Fin 11 → ℚ := ![(11667/32768000000000), (11667/3276800000000), (105003/6553600000000), (35001/819200000000), (245007/3276800000000), (735021/8192000000000), (245007/3276800000000), (35001/819200000000), (107163/6553600000000), (2781/655360000000), (11667/16384000000000)]

def minusWeights0779 : Fin 11 → ℚ := ![(11667/32768000000000), (11667/3276800000000), (105003/6553600000000), (35001/819200000000), (245007/3276800000000), (735021/8192000000000), (245007/3276800000000), (35001/819200000000), (102843/6553600000000), (9429/3276800000000), 0]

theorem checked0779 :
    (∀ i, 0 ≤ plusWeights0779 i) ∧
    (∀ i, 0 ≤ minusWeights0779 i) ∧
    (∀ i, plusCoefficients coefficients0779 upper0779 i = powerCoefficients10 plusWeights0779 i) ∧
    (∀ i, minusCoefficients coefficients0779 upper0779 i = powerCoefficients10 minusWeights0779 i) := by
  decide +kernel

theorem bound0779 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0779 g| ≤ (upper0779 : ℝ) :=
  abs_of_coefficients coefficients0779 upper0779 powerCoefficients10 plusWeights0779 minusWeights0779
    checked0779.1 checked0779.2.1 checked0779.2.2.1 checked0779.2.2.2
    (power_identity10 plusWeights0779) (power_identity10 minusWeights0779) g hg hmax

def envelope0779 : Envelope := ⟨coefficients0779, upper0779, bound0779⟩

def coefficients0780 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/8192), (585/16384), (1305/32768)]

def upper0780 : ℚ := (35001/65536000000000)

def plusWeights0780 : Fin 11 → ℚ := ![(35001/65536000000000), (35001/6553600000000), (315009/13107200000000), (105003/1638400000000), (735021/6553600000000), (2205063/16384000000000), (735021/6553600000000), (105003/1638400000000), (321489/13107200000000), (8343/1310720000000), (35001/32768000000000)]

def minusWeights0780 : Fin 11 → ℚ := ![(35001/65536000000000), (35001/6553600000000), (315009/13107200000000), (105003/1638400000000), (735021/6553600000000), (2205063/16384000000000), (735021/6553600000000), (105003/1638400000000), (308529/13107200000000), (28287/6553600000000), 0]

theorem checked0780 :
    (∀ i, 0 ≤ plusWeights0780 i) ∧
    (∀ i, 0 ≤ minusWeights0780 i) ∧
    (∀ i, plusCoefficients coefficients0780 upper0780 i = powerCoefficients10 plusWeights0780 i) ∧
    (∀ i, minusCoefficients coefficients0780 upper0780 i = powerCoefficients10 minusWeights0780 i) := by
  decide +kernel

theorem bound0780 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0780 g| ≤ (upper0780 : ℝ) :=
  abs_of_coefficients coefficients0780 upper0780 powerCoefficients10 plusWeights0780 minusWeights0780
    checked0780.1 checked0780.2.1 checked0780.2.2.1 checked0780.2.2.2
    (power_identity10 plusWeights0780) (power_identity10 minusWeights0780) g hg hmax

def envelope0780 : Envelope := ⟨coefficients0780, upper0780, bound0780⟩

def coefficients0781 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/2048), (195/4096), (435/8192)]

def upper0781 : ℚ := (11667/16384000000000)

def plusWeights0781 : Fin 11 → ℚ := ![(11667/16384000000000), (11667/1638400000000), (105003/3276800000000), (35001/409600000000), (245007/1638400000000), (735021/4096000000000), (245007/1638400000000), (35001/409600000000), (107163/3276800000000), (2781/327680000000), (11667/8192000000000)]

def minusWeights0781 : Fin 11 → ℚ := ![(11667/16384000000000), (11667/1638400000000), (105003/3276800000000), (35001/409600000000), (245007/1638400000000), (735021/4096000000000), (245007/1638400000000), (35001/409600000000), (102843/3276800000000), (9429/1638400000000), 0]

theorem checked0781 :
    (∀ i, 0 ≤ plusWeights0781 i) ∧
    (∀ i, 0 ≤ minusWeights0781 i) ∧
    (∀ i, plusCoefficients coefficients0781 upper0781 i = powerCoefficients10 plusWeights0781 i) ∧
    (∀ i, minusCoefficients coefficients0781 upper0781 i = powerCoefficients10 minusWeights0781 i) := by
  decide +kernel

theorem bound0781 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0781 g| ≤ (upper0781 : ℝ) :=
  abs_of_coefficients coefficients0781 upper0781 powerCoefficients10 plusWeights0781 minusWeights0781
    checked0781.1 checked0781.2.1 checked0781.2.2.1 checked0781.2.2.2
    (power_identity10 plusWeights0781) (power_identity10 minusWeights0781) g hg hmax

def envelope0781 : Envelope := ⟨coefficients0781, upper0781, bound0781⟩

def coefficients0782 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/256), (3/512), (13/1024), (21/2048), (5/2048)]

def upper0782 : ℚ := (18963/4096000000000)

def plusWeights0782 : Fin 11 → ℚ := ![(18963/4096000000000), (18963/409600000000), (170667/819200000000), (56889/102400000000), (398223/409600000000), (1194669/1024000000000), (399823/409600000000), (58549/102400000000), (191411/819200000000), (32739/512000000000), (18963/2048000000000)]

def minusWeights0782 : Fin 11 → ℚ := ![(18963/4096000000000), (18963/409600000000), (170667/819200000000), (56889/102400000000), (398223/409600000000), (1194669/1024000000000), (396623/409600000000), (55229/102400000000), (149923/819200000000), (29337/1024000000000), 0]

theorem checked0782 :
    (∀ i, 0 ≤ plusWeights0782 i) ∧
    (∀ i, 0 ≤ minusWeights0782 i) ∧
    (∀ i, plusCoefficients coefficients0782 upper0782 i = powerCoefficients10 plusWeights0782 i) ∧
    (∀ i, minusCoefficients coefficients0782 upper0782 i = powerCoefficients10 minusWeights0782 i) := by
  decide +kernel

theorem bound0782 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0782 g| ≤ (upper0782 : ℝ) :=
  abs_of_coefficients coefficients0782 upper0782 powerCoefficients10 plusWeights0782 minusWeights0782
    checked0782.1 checked0782.2.1 checked0782.2.2.1 checked0782.2.2.2
    (power_identity10 plusWeights0782) (power_identity10 minusWeights0782) g hg hmax

def envelope0782 : Envelope := ⟨coefficients0782, upper0782, bound0782⟩

def coefficients0783 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/2048), (-31/8192), (97/8192), (89/16384), (1455/524288)]

def upper0783 : ℚ := (4341347/1048576000000000)

def plusWeights0783 : Fin 11 → ℚ := ![(4341347/1048576000000000), (4341347/104857600000000), (39072123/209715200000000), (13024041/26214400000000), (91168287/104857600000000), (273504861/262144000000000), (91629087/104857600000000), (13474921/26214400000000), (1775539/8388608000000), (30454543/524288000000000), (4341347/524288000000000)]

def minusWeights0783 : Fin 11 → ℚ := ![(4341347/1048576000000000), (4341347/104857600000000), (39072123/209715200000000), (13024041/26214400000000), (91168287/104857600000000), (273504861/262144000000000), (90707487/104857600000000), (12573161/26214400000000), (33755771/209715200000000), (12958927/524288000000000), 0]

theorem checked0783 :
    (∀ i, 0 ≤ plusWeights0783 i) ∧
    (∀ i, 0 ≤ minusWeights0783 i) ∧
    (∀ i, plusCoefficients coefficients0783 upper0783 i = powerCoefficients10 plusWeights0783 i) ∧
    (∀ i, minusCoefficients coefficients0783 upper0783 i = powerCoefficients10 minusWeights0783 i) := by
  decide +kernel

theorem bound0783 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0783 g| ≤ (upper0783 : ℝ) :=
  abs_of_coefficients coefficients0783 upper0783 powerCoefficients10 plusWeights0783 minusWeights0783
    checked0783.1 checked0783.2.1 checked0783.2.2.1 checked0783.2.2.2
    (power_identity10 plusWeights0783) (power_identity10 minusWeights0783) g hg hmax

def envelope0783 : Envelope := ⟨coefficients0783, upper0783, bound0783⟩

def coefficients0784 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/2048), (-31/8192), (673/32768), (701/65536), (5945/524288)]

def upper0784 : ℚ := (887793/209715200000000)

def plusWeights0784 : Fin 11 → ℚ := ![(887793/209715200000000), (887793/20971520000000), (7990137/41943040000000), (2663379/5242880000000), (18643653/20971520000000), (55930959/52428800000000), (18735813/20971520000000), (550711/1048576000000), (45285277/209715200000000), (31036593/524288000000000), (887793/104857600000000)]

def minusWeights0784 : Fin 11 → ℚ := ![(887793/209715200000000), (887793/20971520000000), (7990137/41943040000000), (2663379/5242880000000), (18643653/20971520000000), (55930959/52428800000000), (18551493/20971520000000), (2573203/5242880000000), (34616093/209715200000000), (13353057/524288000000000), 0]

theorem checked0784 :
    (∀ i, 0 ≤ plusWeights0784 i) ∧
    (∀ i, 0 ≤ minusWeights0784 i) ∧
    (∀ i, plusCoefficients coefficients0784 upper0784 i = powerCoefficients10 plusWeights0784 i) ∧
    (∀ i, minusCoefficients coefficients0784 upper0784 i = powerCoefficients10 minusWeights0784 i) := by
  decide +kernel

theorem bound0784 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0784 g| ≤ (upper0784 : ℝ) :=
  abs_of_coefficients coefficients0784 upper0784 powerCoefficients10 plusWeights0784 minusWeights0784
    checked0784.1 checked0784.2.1 checked0784.2.2.1 checked0784.2.2.2
    (power_identity10 plusWeights0784) (power_identity10 minusWeights0784) g hg hmax

def envelope0784 : Envelope := ⟨coefficients0784, upper0784, bound0784⟩

def coefficients0785 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/2048), (19/8192), (97/8192), (89/16384), (1455/524288)]

def upper0785 : ℚ := (4981347/1048576000000000)

def plusWeights0785 : Fin 11 → ℚ := ![(4981347/1048576000000000), (4981347/104857600000000), (44832123/209715200000000), (14944041/26214400000000), (104608287/104857600000000), (313824861/262144000000000), (105069087/104857600000000), (15410921/26214400000000), (2021299/8388608000000), (34614543/524288000000000), (4981347/524288000000000)]

def minusWeights0785 : Fin 11 → ℚ := ![(4981347/1048576000000000), (4981347/104857600000000), (44832123/209715200000000), (14944041/26214400000000), (104608287/104857600000000), (313824861/262144000000000), (104147487/104857600000000), (14477161/26214400000000), (39131771/209715200000000), (15198927/524288000000000), 0]

theorem checked0785 :
    (∀ i, 0 ≤ plusWeights0785 i) ∧
    (∀ i, 0 ≤ minusWeights0785 i) ∧
    (∀ i, plusCoefficients coefficients0785 upper0785 i = powerCoefficients10 plusWeights0785 i) ∧
    (∀ i, minusCoefficients coefficients0785 upper0785 i = powerCoefficients10 minusWeights0785 i) := by
  decide +kernel

theorem bound0785 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0785 g| ≤ (upper0785 : ℝ) :=
  abs_of_coefficients coefficients0785 upper0785 powerCoefficients10 plusWeights0785 minusWeights0785
    checked0785.1 checked0785.2.1 checked0785.2.2.1 checked0785.2.2.2
    (power_identity10 plusWeights0785) (power_identity10 minusWeights0785) g hg hmax

def envelope0785 : Envelope := ⟨coefficients0785, upper0785, bound0785⟩

def coefficients0786 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/1024), (-89/4096), (-111/4096), (-2213/65536), (-1721/131072)]

def upper0786 : ℚ := (3150819/1310720000000000)

def plusWeights0786 : Fin 11 → ℚ := ![(3150819/1310720000000000), (3150819/131072000000000), (28357371/262144000000000), (9452457/32768000000000), (66167199/131072000000000), (198501597/327680000000000), (66807199/131072000000000), (10021257/32768000000000), (34257531/262144000000000), (4780953/131072000000000), (3150819/655360000000000)]

def minusWeights0786 : Fin 11 → ℚ := ![(3150819/1310720000000000), (3150819/131072000000000), (28357371/262144000000000), (9452457/32768000000000), (66167199/131072000000000), (198501597/327680000000000), (65527199/131072000000000), (8883657/32768000000000), (22457211/262144000000000), (304137/26214400000000), 0]

theorem checked0786 :
    (∀ i, 0 ≤ plusWeights0786 i) ∧
    (∀ i, 0 ≤ minusWeights0786 i) ∧
    (∀ i, plusCoefficients coefficients0786 upper0786 i = powerCoefficients10 plusWeights0786 i) ∧
    (∀ i, minusCoefficients coefficients0786 upper0786 i = powerCoefficients10 minusWeights0786 i) := by
  decide +kernel

theorem bound0786 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0786 g| ≤ (upper0786 : ℝ) :=
  abs_of_coefficients coefficients0786 upper0786 powerCoefficients10 plusWeights0786 minusWeights0786
    checked0786.1 checked0786.2.1 checked0786.2.2.1 checked0786.2.2.2
    (power_identity10 plusWeights0786) (power_identity10 minusWeights0786) g hg hmax

def envelope0786 : Envelope := ⟨coefficients0786, upper0786, bound0786⟩

def coefficients0787 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/1024), (-35/4096), (-45/4096), (-405/65536), (-225/131072)]

def upper0787 : ℚ := (205107/52428800000000)

def plusWeights0787 : Fin 11 → ℚ := ![(205107/52428800000000), (205107/5242880000000), (1845963/10485760000000), (615321/1310720000000), (4307247/5242880000000), (12921741/13107200000000), (4332847/5242880000000), (639801/1310720000000), (2125131/10485760000000), (1464413/26214400000000), (205107/26214400000000)]

def minusWeights0787 : Fin 11 → ℚ := ![(205107/52428800000000), (205107/5242880000000), (1845963/10485760000000), (615321/1310720000000), (4307247/5242880000000), (12921741/13107200000000), (4281647/5242880000000), (590841/1310720000000), (313359/2097152000000), (586657/26214400000000), 0]

theorem checked0787 :
    (∀ i, 0 ≤ plusWeights0787 i) ∧
    (∀ i, 0 ≤ minusWeights0787 i) ∧
    (∀ i, plusCoefficients coefficients0787 upper0787 i = powerCoefficients10 plusWeights0787 i) ∧
    (∀ i, minusCoefficients coefficients0787 upper0787 i = powerCoefficients10 minusWeights0787 i) := by
  decide +kernel

theorem bound0787 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0787 g| ≤ (upper0787 : ℝ) :=
  abs_of_coefficients coefficients0787 upper0787 powerCoefficients10 plusWeights0787 minusWeights0787
    checked0787.1 checked0787.2.1 checked0787.2.2.1 checked0787.2.2.2
    (power_identity10 plusWeights0787) (power_identity10 minusWeights0787) g hg hmax

def envelope0787 : Envelope := ⟨coefficients0787, upper0787, bound0787⟩

def coefficients0788 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/1024), (-25/4096), (-35/4096), (-315/65536), (-175/131072)]

def upper0788 : ℚ := (219261/52428800000000)

def plusWeights0788 : Fin 11 → ℚ := ![(219261/52428800000000), (219261/5242880000000), (1973349/10485760000000), (657783/1310720000000), (4604481/5242880000000), (13813443/13107200000000), (4630081/5242880000000), (682583/1310720000000), (2260453/10485760000000), (1555699/26214400000000), (219261/26214400000000)]

def minusWeights0788 : Fin 11 → ℚ := ![(219261/52428800000000), (219261/5242880000000), (1973349/10485760000000), (657783/1310720000000), (4604481/5242880000000), (13813443/13107200000000), (4578881/5242880000000), (632983/1310720000000), (337249/2097152000000), (636911/26214400000000), 0]

theorem checked0788 :
    (∀ i, 0 ≤ plusWeights0788 i) ∧
    (∀ i, 0 ≤ minusWeights0788 i) ∧
    (∀ i, plusCoefficients coefficients0788 upper0788 i = powerCoefficients10 plusWeights0788 i) ∧
    (∀ i, minusCoefficients coefficients0788 upper0788 i = powerCoefficients10 minusWeights0788 i) := by
  decide +kernel

theorem bound0788 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0788 g| ≤ (upper0788 : ℝ) :=
  abs_of_coefficients coefficients0788 upper0788 powerCoefficients10 plusWeights0788 minusWeights0788
    checked0788.1 checked0788.2.1 checked0788.2.2.1 checked0788.2.2.2
    (power_identity10 plusWeights0788) (power_identity10 minusWeights0788) g hg hmax

def envelope0788 : Envelope := ⟨coefficients0788, upper0788, bound0788⟩

def coefficients0789 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/1024), (-15/4096), (-25/4096), (-225/65536), (-125/131072)]

def upper0789 : ℚ := (46683/10485760000000)

def plusWeights0789 : Fin 11 → ℚ := ![(46683/10485760000000), (46683/1048576000000), (420147/2097152000000), (140049/262144000000), (980343/1048576000000), (2941029/2621440000000), (985463/1048576000000), (145073/262144000000), (95831/419430400000), (329397/5242880000000), (46683/5242880000000)]

def minusWeights0789 : Fin 11 → ℚ := ![(46683/10485760000000), (46683/1048576000000), (420147/2097152000000), (140049/262144000000), (980343/1048576000000), (2941029/2621440000000), (975223/1048576000000), (5401/10485760000), (361139/2097152000000), (137433/5242880000000), 0]

theorem checked0789 :
    (∀ i, 0 ≤ plusWeights0789 i) ∧
    (∀ i, 0 ≤ minusWeights0789 i) ∧
    (∀ i, plusCoefficients coefficients0789 upper0789 i = powerCoefficients10 plusWeights0789 i) ∧
    (∀ i, minusCoefficients coefficients0789 upper0789 i = powerCoefficients10 minusWeights0789 i) := by
  decide +kernel

theorem bound0789 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0789 g| ≤ (upper0789 : ℝ) :=
  abs_of_coefficients coefficients0789 upper0789 powerCoefficients10 plusWeights0789 minusWeights0789
    checked0789.1 checked0789.2.1 checked0789.2.2.1 checked0789.2.2.2
    (power_identity10 plusWeights0789) (power_identity10 minusWeights0789) g hg hmax

def envelope0789 : Envelope := ⟨coefficients0789, upper0789, bound0789⟩

def coefficients0790 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/1024), (5/2048), (275/32768), (375/65536), (1275/524288)]

def upper0790 : ℚ := (1094051/209715200000000)

def plusWeights0790 : Fin 11 → ℚ := ![(1094051/209715200000000), (1094051/20971520000000), (9846459/41943040000000), (3282153/5242880000000), (22975071/20971520000000), (68925213/52428800000000), (23077471/20971520000000), (3385833/5242880000000), (11109499/41943040000000), (1522651/20971520000000), (1094051/104857600000000)]

def minusWeights0790 : Fin 11 → ℚ := ![(1094051/209715200000000), (1094051/20971520000000), (9846459/41943040000000), (3282153/5242880000000), (22975071/20971520000000), (68925213/52428800000000), (22872671/20971520000000), (3178473/5242880000000), (8583419/41943040000000), (665451/20971520000000), 0]

theorem checked0790 :
    (∀ i, 0 ≤ plusWeights0790 i) ∧
    (∀ i, 0 ≤ minusWeights0790 i) ∧
    (∀ i, plusCoefficients coefficients0790 upper0790 i = powerCoefficients10 plusWeights0790 i) ∧
    (∀ i, minusCoefficients coefficients0790 upper0790 i = powerCoefficients10 minusWeights0790 i) := by
  decide +kernel

theorem bound0790 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0790 g| ≤ (upper0790 : ℝ) :=
  abs_of_coefficients coefficients0790 upper0790 powerCoefficients10 plusWeights0790 minusWeights0790
    checked0790.1 checked0790.2.1 checked0790.2.2.1 checked0790.2.2.2
    (power_identity10 plusWeights0790) (power_identity10 minusWeights0790) g hg hmax

def envelope0790 : Envelope := ⟨coefficients0790, upper0790, bound0790⟩

def coefficients0791 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/1024), (5/1024), (35/8192), (25/16384), (125/262144)]

def upper0791 : ℚ := (113569/20971520000000)

def plusWeights0791 : Fin 11 → ℚ := ![(113569/20971520000000), (113569/2097152000000), (1022121/4194304000000), (340707/524288000000), (2384949/2097152000000), (7154847/5242880000000), (2395189/2097152000000), (351203/524288000000), (5756621/20971520000000), (788917/10485760000000), (113569/10485760000000)]

def minusWeights0791 : Fin 11 → ℚ := ![(113569/20971520000000), (113569/2097152000000), (1022121/4194304000000), (340707/524288000000), (2384949/2097152000000), (7154847/5242880000000), (2374709/2097152000000), (330211/524288000000), (4464589/20971520000000), (346773/10485760000000), 0]

theorem checked0791 :
    (∀ i, 0 ≤ plusWeights0791 i) ∧
    (∀ i, 0 ≤ minusWeights0791 i) ∧
    (∀ i, plusCoefficients coefficients0791 upper0791 i = powerCoefficients10 plusWeights0791 i) ∧
    (∀ i, minusCoefficients coefficients0791 upper0791 i = powerCoefficients10 minusWeights0791 i) := by
  decide +kernel

theorem bound0791 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0791 g| ≤ (upper0791 : ℝ) :=
  abs_of_coefficients coefficients0791 upper0791 powerCoefficients10 plusWeights0791 minusWeights0791
    checked0791.1 checked0791.2.1 checked0791.2.2.1 checked0791.2.2.2
    (power_identity10 plusWeights0791) (power_identity10 minusWeights0791) g hg hmax

def envelope0791 : Envelope := ⟨coefficients0791, upper0791, bound0791⟩

def coefficients0792 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/1024), (69/8192), (21/4096), (1/256), (15/16384)]

def upper0792 : ℚ := (253411/32768000000000)

def plusWeights0792 : Fin 11 → ℚ := ![(253411/32768000000000), (253411/3276800000000), (2280699/6553600000000), (760233/819200000000), (5321631/3276800000000), (15964893/8192000000000), (5344031/3276800000000), (783323/819200000000), (513279/1310720000000), (1758199/16384000000000), (253411/16384000000000)]

def minusWeights0792 : Fin 11 → ℚ := ![(253411/32768000000000), (253411/3276800000000), (2280699/6553600000000), (760233/819200000000), (5321631/3276800000000), (15964893/8192000000000), (5299231/3276800000000), (737143/819200000000), (1995003/6553600000000), (775911/16384000000000), 0]

theorem checked0792 :
    (∀ i, 0 ≤ plusWeights0792 i) ∧
    (∀ i, 0 ≤ minusWeights0792 i) ∧
    (∀ i, plusCoefficients coefficients0792 upper0792 i = powerCoefficients10 plusWeights0792 i) ∧
    (∀ i, minusCoefficients coefficients0792 upper0792 i = powerCoefficients10 minusWeights0792 i) := by
  decide +kernel

theorem bound0792 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0792 g| ≤ (upper0792 : ℝ) :=
  abs_of_coefficients coefficients0792 upper0792 powerCoefficients10 plusWeights0792 minusWeights0792
    checked0792.1 checked0792.2.1 checked0792.2.2.1 checked0792.2.2.2
    (power_identity10 plusWeights0792) (power_identity10 minusWeights0792) g hg hmax

def envelope0792 : Envelope := ⟨coefficients0792, upper0792, bound0792⟩

def coefficients0793 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/1024), (119/8192), (21/4096), (1/256), (15/16384)]

def upper0793 : ℚ := (273411/32768000000000)

def plusWeights0793 : Fin 11 → ℚ := ![(273411/32768000000000), (273411/3276800000000), (2460699/6553600000000), (820233/819200000000), (5741631/3276800000000), (17224893/8192000000000), (5764031/3276800000000), (843823/819200000000), (551679/1310720000000), (1888199/16384000000000), (273411/16384000000000)]

def minusWeights0793 : Fin 11 → ℚ := ![(273411/32768000000000), (273411/3276800000000), (2460699/6553600000000), (820233/819200000000), (5741631/3276800000000), (17224893/8192000000000), (5719231/3276800000000), (796643/819200000000), (2163003/6553600000000), (845911/16384000000000), 0]

theorem checked0793 :
    (∀ i, 0 ≤ plusWeights0793 i) ∧
    (∀ i, 0 ≤ minusWeights0793 i) ∧
    (∀ i, plusCoefficients coefficients0793 upper0793 i = powerCoefficients10 plusWeights0793 i) ∧
    (∀ i, minusCoefficients coefficients0793 upper0793 i = powerCoefficients10 minusWeights0793 i) := by
  decide +kernel

theorem bound0793 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0793 g| ≤ (upper0793 : ℝ) :=
  abs_of_coefficients coefficients0793 upper0793 powerCoefficients10 plusWeights0793 minusWeights0793
    checked0793.1 checked0793.2.1 checked0793.2.2.1 checked0793.2.2.2
    (power_identity10 plusWeights0793) (power_identity10 minusWeights0793) g hg hmax

def envelope0793 : Envelope := ⟨coefficients0793, upper0793, bound0793⟩

def coefficients0794 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/1024), (119/8192), (9/1024), (31/4096), (15/8192)]

def upper0794 : ℚ := (137367/16384000000000)

def plusWeights0794 : Fin 11 → ℚ := ![(137367/16384000000000), (137367/1638400000000), (1236303/3276800000000), (412101/409600000000), (2884707/1638400000000), (8654121/4096000000000), (2895907/1638400000000), (52987/51200000000), (1385271/3276800000000), (948037/8192000000000), (137367/8192000000000)]

def minusWeights0794 : Fin 11 → ℚ := ![(137367/16384000000000), (137367/1638400000000), (1236303/3276800000000), (412101/409600000000), (2884707/1638400000000), (8654121/4096000000000), (2873507/1638400000000), (200153/204800000000), (217467/655360000000), (425633/8192000000000), 0]

theorem checked0794 :
    (∀ i, 0 ≤ plusWeights0794 i) ∧
    (∀ i, 0 ≤ minusWeights0794 i) ∧
    (∀ i, plusCoefficients coefficients0794 upper0794 i = powerCoefficients10 plusWeights0794 i) ∧
    (∀ i, minusCoefficients coefficients0794 upper0794 i = powerCoefficients10 minusWeights0794 i) := by
  decide +kernel

theorem bound0794 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0794 g| ≤ (upper0794 : ℝ) :=
  abs_of_coefficients coefficients0794 upper0794 powerCoefficients10 plusWeights0794 minusWeights0794
    checked0794.1 checked0794.2.1 checked0794.2.2.1 checked0794.2.2.2
    (power_identity10 plusWeights0794) (power_identity10 minusWeights0794) g hg hmax

def envelope0794 : Envelope := ⟨coefficients0794, upper0794, bound0794⟩

def coefficients0795 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/2048), (5/2048), (35/4096), (125/16384), (1425/524288)]

def upper0795 : ℚ := (1606777/209715200000000)

def plusWeights0795 : Fin 11 → ℚ := ![(1606777/209715200000000), (1606777/20971520000000), (14460993/41943040000000), (4820331/5242880000000), (33742317/20971520000000), (101226951/52428800000000), (33895917/20971520000000), (4975211/5242880000000), (16338497/41943040000000), (2240281/20971520000000), (1606777/104857600000000)]

def minusWeights0795 : Fin 11 → ℚ := ![(1606777/209715200000000), (1606777/20971520000000), (14460993/41943040000000), (4820331/5242880000000), (33742317/20971520000000), (101226951/52428800000000), (33588717/20971520000000), (4665451/5242880000000), (12583489/41943040000000), (973273/20971520000000), 0]

theorem checked0795 :
    (∀ i, 0 ≤ plusWeights0795 i) ∧
    (∀ i, 0 ≤ minusWeights0795 i) ∧
    (∀ i, plusCoefficients coefficients0795 upper0795 i = powerCoefficients10 plusWeights0795 i) ∧
    (∀ i, minusCoefficients coefficients0795 upper0795 i = powerCoefficients10 minusWeights0795 i) := by
  decide +kernel

theorem bound0795 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0795 g| ≤ (upper0795 : ℝ) :=
  abs_of_coefficients coefficients0795 upper0795 powerCoefficients10 plusWeights0795 minusWeights0795
    checked0795.1 checked0795.2.1 checked0795.2.2.1 checked0795.2.2.2
    (power_identity10 plusWeights0795) (power_identity10 minusWeights0795) g hg hmax

def envelope0795 : Envelope := ⟨coefficients0795, upper0795, bound0795⟩

def coefficients0796 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/2048), (5/1024), (15/4096), (25/8192), (275/524288)]

def upper0796 : ℚ := (1646731/209715200000000)

def plusWeights0796 : Fin 11 → ℚ := ![(1646731/209715200000000), (1646731/20971520000000), (14820579/41943040000000), (4940193/5242880000000), (34581351/20971520000000), (103744053/52428800000000), (34734951/20971520000000), (5096353/5242880000000), (3345351/8388608000000), (2293451/20971520000000), (1646731/104857600000000)]

def minusWeights0796 : Fin 11 → ℚ := ![(1646731/209715200000000), (1646731/20971520000000), (14820579/41943040000000), (4940193/5242880000000), (34581351/20971520000000), (103744053/52428800000000), (34427751/20971520000000), (4784033/5242880000000), (12914403/41943040000000), (1000011/20971520000000), 0]

theorem checked0796 :
    (∀ i, 0 ≤ plusWeights0796 i) ∧
    (∀ i, 0 ≤ minusWeights0796 i) ∧
    (∀ i, plusCoefficients coefficients0796 upper0796 i = powerCoefficients10 plusWeights0796 i) ∧
    (∀ i, minusCoefficients coefficients0796 upper0796 i = powerCoefficients10 minusWeights0796 i) := by
  decide +kernel

theorem bound0796 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0796 g| ≤ (upper0796 : ℝ) :=
  abs_of_coefficients coefficients0796 upper0796 powerCoefficients10 plusWeights0796 minusWeights0796
    checked0796.1 checked0796.2.1 checked0796.2.2.1 checked0796.2.2.2
    (power_identity10 plusWeights0796) (power_identity10 minusWeights0796) g hg hmax

def envelope0796 : Envelope := ⟨coefficients0796, upper0796, bound0796⟩

def coefficients0797 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/2048), (5/1024), (5/512), (25/4096), (1275/524288)]

def upper0797 : ℚ := (1660211/209715200000000)

def plusWeights0797 : Fin 11 → ℚ := ![(1660211/209715200000000), (1660211/20971520000000), (14941899/41943040000000), (4980633/5242880000000), (34864431/20971520000000), (104593293/52428800000000), (35018031/20971520000000), (5136793/5242880000000), (3370127/8388608000000), (461911/4194304000000), (1660211/104857600000000)]

def minusWeights0797 : Fin 11 → ℚ := ![(1660211/209715200000000), (1660211/20971520000000), (14941899/41943040000000), (4980633/5242880000000), (34864431/20971520000000), (104593293/52428800000000), (34710831/20971520000000), (4824473/5242880000000), (13033163/41943040000000), (1010867/20971520000000), 0]

theorem checked0797 :
    (∀ i, 0 ≤ plusWeights0797 i) ∧
    (∀ i, 0 ≤ minusWeights0797 i) ∧
    (∀ i, plusCoefficients coefficients0797 upper0797 i = powerCoefficients10 plusWeights0797 i) ∧
    (∀ i, minusCoefficients coefficients0797 upper0797 i = powerCoefficients10 minusWeights0797 i) := by
  decide +kernel

theorem bound0797 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0797 g| ≤ (upper0797 : ℝ) :=
  abs_of_coefficients coefficients0797 upper0797 powerCoefficients10 plusWeights0797 minusWeights0797
    checked0797.1 checked0797.2.1 checked0797.2.2.1 checked0797.2.2.2
    (power_identity10 plusWeights0797) (power_identity10 minusWeights0797) g hg hmax

def envelope0797 : Envelope := ⟨coefficients0797, upper0797, bound0797⟩

def coefficients0798 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/2048), (5/1024), (405/32768), (545/65536), (4765/524288)]

def upper0798 : ℚ := (8331273/1048576000000000)

def plusWeights0798 : Fin 11 → ℚ := ![(8331273/1048576000000000), (8331273/104857600000000), (74981457/209715200000000), (24993819/26214400000000), (174956733/104857600000000), (524870199/262144000000000), (175724733/104857600000000), (25774619/26214400000000), (84530577/209715200000000), (2316733/20971520000000), (8331273/524288000000000)]

def minusWeights0798 : Fin 11 → ℚ := ![(8331273/1048576000000000), (8331273/104857600000000), (74981457/209715200000000), (24993819/26214400000000), (174956733/104857600000000), (524870199/262144000000000), (174188733/104857600000000), (24213019/26214400000000), (65432337/209715200000000), (5078881/104857600000000), 0]

theorem checked0798 :
    (∀ i, 0 ≤ plusWeights0798 i) ∧
    (∀ i, 0 ≤ minusWeights0798 i) ∧
    (∀ i, plusCoefficients coefficients0798 upper0798 i = powerCoefficients10 plusWeights0798 i) ∧
    (∀ i, minusCoefficients coefficients0798 upper0798 i = powerCoefficients10 minusWeights0798 i) := by
  decide +kernel

theorem bound0798 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0798 g| ≤ (upper0798 : ℝ) :=
  abs_of_coefficients coefficients0798 upper0798 powerCoefficients10 plusWeights0798 minusWeights0798
    checked0798.1 checked0798.2.1 checked0798.2.2.1 checked0798.2.2.2
    (power_identity10 plusWeights0798) (power_identity10 minusWeights0798) g hg hmax

def envelope0798 : Envelope := ⟨coefficients0798, upper0798, bound0798⟩

def coefficients0799 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/128), (3/256), (21/1024), (1/64), (15/4096)]

def upper0799 : ℚ := (75411/8192000000000)

def plusWeights0799 : Fin 11 → ℚ := ![(75411/8192000000000), (75411/819200000000), (678699/1638400000000), (226233/204800000000), (1583631/819200000000), (4750893/2048000000000), (1590031/819200000000), (232873/204800000000), (152319/327680000000), (521199/4096000000000), (75411/4096000000000)]

def minusWeights0799 : Fin 11 → ℚ := ![(75411/8192000000000), (75411/819200000000), (678699/1638400000000), (226233/204800000000), (1583631/819200000000), (4750893/2048000000000), (1577231/819200000000), (219593/204800000000), (595803/1638400000000), (232911/4096000000000), 0]

theorem checked0799 :
    (∀ i, 0 ≤ plusWeights0799 i) ∧
    (∀ i, 0 ≤ minusWeights0799 i) ∧
    (∀ i, plusCoefficients coefficients0799 upper0799 i = powerCoefficients10 plusWeights0799 i) ∧
    (∀ i, minusCoefficients coefficients0799 upper0799 i = powerCoefficients10 minusWeights0799 i) := by
  decide +kernel

theorem bound0799 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0799 g| ≤ (upper0799 : ℝ) :=
  abs_of_coefficients coefficients0799 upper0799 powerCoefficients10 plusWeights0799 minusWeights0799
    checked0799.1 checked0799.2.1 checked0799.2.2.1 checked0799.2.2.2
    (power_identity10 plusWeights0799) (power_identity10 minusWeights0799) g hg hmax

def envelope0799 : Envelope := ⟨coefficients0799, upper0799, bound0799⟩

end BilayerDressed.CubicQuarticEnvelopes

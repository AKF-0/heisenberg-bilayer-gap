import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0800 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/128), (3/256), (47/2048), (37/2048), (35/8192)]

def upper0800 : ℚ := (151263/16384000000000)

def plusWeights0800 : Fin 11 → ℚ := ![(151263/16384000000000), (151263/1638400000000), (1361367/3276800000000), (453789/409600000000), (3176523/1638400000000), (9529569/4096000000000), (3189323/1638400000000), (467069/409600000000), (1527239/3276800000000), (1045023/8192000000000), (151263/8192000000000)]

def minusWeights0800 : Fin 11 → ℚ := ![(151263/16384000000000), (151263/1638400000000), (1361367/3276800000000), (453789/409600000000), (3176523/1638400000000), (9529569/4096000000000), (3163723/1638400000000), (440509/409600000000), (239099/655360000000), (467607/8192000000000), 0]

theorem checked0800 :
    (∀ i, 0 ≤ plusWeights0800 i) ∧
    (∀ i, 0 ≤ minusWeights0800 i) ∧
    (∀ i, plusCoefficients coefficients0800 upper0800 i = powerCoefficients10 plusWeights0800 i) ∧
    (∀ i, minusCoefficients coefficients0800 upper0800 i = powerCoefficients10 minusWeights0800 i) := by
  decide +kernel

theorem bound0800 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0800 g| ≤ (upper0800 : ℝ) :=
  abs_of_coefficients coefficients0800 upper0800 powerCoefficients10 plusWeights0800 minusWeights0800
    checked0800.1 checked0800.2.1 checked0800.2.2.1 checked0800.2.2.2
    (power_identity10 plusWeights0800) (power_identity10 minusWeights0800) g hg hmax

def envelope0800 : Envelope := ⟨coefficients0800, upper0800, bound0800⟩

def coefficients0801 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/128), (3/256), (57/2048), (47/2048), (45/8192)]

def upper0801 : ℚ := (30429/3276800000000)

def plusWeights0801 : Fin 11 → ℚ := ![(30429/3276800000000), (30429/327680000000), (273861/655360000000), (91287/81920000000), (639009/327680000000), (1917027/819200000000), (641569/327680000000), (93943/81920000000), (1535337/3276800000000), (1050273/8192000000000), (30429/1638400000000)]

def minusWeights0801 : Fin 11 → ℚ := ![(30429/3276800000000), (30429/327680000000), (273861/655360000000), (91287/81920000000), (639009/327680000000), (1917027/819200000000), (636449/327680000000), (88631/81920000000), (1203273/3276800000000), (471177/8192000000000), 0]

theorem checked0801 :
    (∀ i, 0 ≤ plusWeights0801 i) ∧
    (∀ i, 0 ≤ minusWeights0801 i) ∧
    (∀ i, plusCoefficients coefficients0801 upper0801 i = powerCoefficients10 plusWeights0801 i) ∧
    (∀ i, minusCoefficients coefficients0801 upper0801 i = powerCoefficients10 minusWeights0801 i) := by
  decide +kernel

theorem bound0801 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0801 g| ≤ (upper0801 : ℝ) :=
  abs_of_coefficients coefficients0801 upper0801 powerCoefficients10 plusWeights0801 minusWeights0801
    checked0801.1 checked0801.2.1 checked0801.2.2.1 checked0801.2.2.2
    (power_identity10 plusWeights0801) (power_identity10 minusWeights0801) g hg hmax

def envelope0801 : Envelope := ⟨coefficients0801, upper0801, bound0801⟩

def coefficients0802 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/128), (3/256), (67/2048), (57/2048), (55/8192)]

def upper0802 : ℚ := (153027/16384000000000)

def plusWeights0802 : Fin 11 → ℚ := ![(153027/16384000000000), (153027/1638400000000), (1377243/3276800000000), (459081/409600000000), (3213567/1638400000000), (9640701/4096000000000), (3226367/1638400000000), (472361/409600000000), (308687/655360000000), (1055523/8192000000000), (153027/8192000000000)]

def minusWeights0802 : Fin 11 → ℚ := ![(153027/16384000000000), (153027/1638400000000), (1377243/3276800000000), (459081/409600000000), (3213567/1638400000000), (9640701/4096000000000), (3200767/1638400000000), (445801/409600000000), (1211051/3276800000000), (474747/8192000000000), 0]

theorem checked0802 :
    (∀ i, 0 ≤ plusWeights0802 i) ∧
    (∀ i, 0 ≤ minusWeights0802 i) ∧
    (∀ i, plusCoefficients coefficients0802 upper0802 i = powerCoefficients10 plusWeights0802 i) ∧
    (∀ i, minusCoefficients coefficients0802 upper0802 i = powerCoefficients10 minusWeights0802 i) := by
  decide +kernel

theorem bound0802 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0802 g| ≤ (upper0802 : ℝ) :=
  abs_of_coefficients coefficients0802 upper0802 powerCoefficients10 plusWeights0802 minusWeights0802
    checked0802.1 checked0802.2.1 checked0802.2.2.1 checked0802.2.2.2
    (power_identity10 plusWeights0802) (power_identity10 minusWeights0802) g hg hmax

def envelope0802 : Envelope := ⟨coefficients0802, upper0802, bound0802⟩

def coefficients0803 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/128), (3/256), (77/2048), (67/2048), (65/8192)]

def upper0803 : ℚ := (153909/16384000000000)

def plusWeights0803 : Fin 11 → ℚ := ![(153909/16384000000000), (153909/1638400000000), (1385181/3276800000000), (461727/409600000000), (3232089/1638400000000), (9696267/4096000000000), (3244889/1638400000000), (475007/409600000000), (1551533/3276800000000), (1060773/8192000000000), (153909/8192000000000)]

def minusWeights0803 : Fin 11 → ℚ := ![(153909/16384000000000), (153909/1638400000000), (1385181/3276800000000), (461727/409600000000), (3232089/1638400000000), (9696267/4096000000000), (3219289/1638400000000), (448447/409600000000), (1218829/3276800000000), (478317/8192000000000), 0]

theorem checked0803 :
    (∀ i, 0 ≤ plusWeights0803 i) ∧
    (∀ i, 0 ≤ minusWeights0803 i) ∧
    (∀ i, plusCoefficients coefficients0803 upper0803 i = powerCoefficients10 plusWeights0803 i) ∧
    (∀ i, minusCoefficients coefficients0803 upper0803 i = powerCoefficients10 minusWeights0803 i) := by
  decide +kernel

theorem bound0803 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0803 g| ≤ (upper0803 : ℝ) :=
  abs_of_coefficients coefficients0803 upper0803 powerCoefficients10 plusWeights0803 minusWeights0803
    checked0803.1 checked0803.2.1 checked0803.2.2.1 checked0803.2.2.2
    (power_identity10 plusWeights0803) (power_identity10 minusWeights0803) g hg hmax

def envelope0803 : Envelope := ⟨coefficients0803, upper0803, bound0803⟩

def coefficients0804 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/1024), (13/8192), (651/32768), (587/65536), (2285/524288)]

def upper0804 : ℚ := (9600569/1048576000000000)

def plusWeights0804 : Fin 11 → ℚ := ![(9600569/1048576000000000), (9600569/104857600000000), (86405121/209715200000000), (28801707/26214400000000), (201611949/104857600000000), (604835847/262144000000000), (202533549/104857600000000), (29727467/26214400000000), (3904233/8388608000000), (66897461/524288000000000), (9600569/524288000000000)]

def minusWeights0804 : Fin 11 → ℚ := ![(9600569/1048576000000000), (9600569/104857600000000), (86405121/209715200000000), (28801707/26214400000000), (201611949/104857600000000), (604835847/262144000000000), (200690349/104857600000000), (27875947/26214400000000), (75204417/209715200000000), (29108229/524288000000000), 0]

theorem checked0804 :
    (∀ i, 0 ≤ plusWeights0804 i) ∧
    (∀ i, 0 ≤ minusWeights0804 i) ∧
    (∀ i, plusCoefficients coefficients0804 upper0804 i = powerCoefficients10 plusWeights0804 i) ∧
    (∀ i, minusCoefficients coefficients0804 upper0804 i = powerCoefficients10 minusWeights0804 i) := by
  decide +kernel

theorem bound0804 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0804 g| ≤ (upper0804 : ℝ) :=
  abs_of_coefficients coefficients0804 upper0804 powerCoefficients10 plusWeights0804 minusWeights0804
    checked0804.1 checked0804.2.1 checked0804.2.2.1 checked0804.2.2.2
    (power_identity10 plusWeights0804) (power_identity10 minusWeights0804) g hg hmax

def envelope0804 : Envelope := ⟨coefficients0804, upper0804, bound0804⟩

def coefficients0805 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/1024), (13/8192), (1311/32768), (1607/65536), (12725/524288)]

def upper0805 : ℚ := (9830177/1048576000000000)

def plusWeights0805 : Fin 11 → ℚ := ![(9830177/1048576000000000), (9830177/104857600000000), (88471593/209715200000000), (29490531/26214400000000), (206433717/104857600000000), (619301151/262144000000000), (207355317/104857600000000), (30416291/26214400000000), (99714537/209715200000000), (68264861/524288000000000), (9830177/524288000000000)]

def minusWeights0805 : Fin 11 → ℚ := ![(9830177/1048576000000000), (9830177/104857600000000), (88471593/209715200000000), (29490531/26214400000000), (206433717/104857600000000), (619301151/262144000000000), (205512117/104857600000000), (28564771/26214400000000), (77228649/209715200000000), (30036909/524288000000000), 0]

theorem checked0805 :
    (∀ i, 0 ≤ plusWeights0805 i) ∧
    (∀ i, 0 ≤ minusWeights0805 i) ∧
    (∀ i, plusCoefficients coefficients0805 upper0805 i = powerCoefficients10 plusWeights0805 i) ∧
    (∀ i, minusCoefficients coefficients0805 upper0805 i = powerCoefficients10 minusWeights0805 i) := by
  decide +kernel

theorem bound0805 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0805 g| ≤ (upper0805 : ℝ) :=
  abs_of_coefficients coefficients0805 upper0805 powerCoefficients10 plusWeights0805 minusWeights0805
    checked0805.1 checked0805.2.1 checked0805.2.2.1 checked0805.2.2.2
    (power_identity10 plusWeights0805) (power_identity10 minusWeights0805) g hg hmax

def envelope0805 : Envelope := ⟨coefficients0805, upper0805, bound0805⟩

def coefficients0806 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/1024), (13/8192), (1461/32768), (1757/65536), (14225/524288)]

def upper0806 : ℚ := (9880877/1048576000000000)

def plusWeights0806 : Fin 11 → ℚ := ![(9880877/1048576000000000), (9880877/104857600000000), (88927893/209715200000000), (29642631/26214400000000), (207498417/104857600000000), (622495251/262144000000000), (208420017/104857600000000), (30568391/26214400000000), (100180437/209715200000000), (68567561/524288000000000), (9880877/524288000000000)]

def minusWeights0806 : Fin 11 → ℚ := ![(9880877/1048576000000000), (9880877/104857600000000), (88927893/209715200000000), (29642631/26214400000000), (207498417/104857600000000), (622495251/262144000000000), (206576817/104857600000000), (28716871/26214400000000), (77675349/209715200000000), (30241209/524288000000000), 0]

theorem checked0806 :
    (∀ i, 0 ≤ plusWeights0806 i) ∧
    (∀ i, 0 ≤ minusWeights0806 i) ∧
    (∀ i, plusCoefficients coefficients0806 upper0806 i = powerCoefficients10 plusWeights0806 i) ∧
    (∀ i, minusCoefficients coefficients0806 upper0806 i = powerCoefficients10 minusWeights0806 i) := by
  decide +kernel

theorem bound0806 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0806 g| ≤ (upper0806 : ℝ) :=
  abs_of_coefficients coefficients0806 upper0806 powerCoefficients10 plusWeights0806 minusWeights0806
    checked0806.1 checked0806.2.1 checked0806.2.2.1 checked0806.2.2.2
    (power_identity10 plusWeights0806) (power_identity10 minusWeights0806) g hg hmax

def envelope0806 : Envelope := ⟨coefficients0806, upper0806, bound0806⟩

def coefficients0807 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/512), (-5/512), (-15/1024), (-135/16384), (-75/32768)]

def upper0807 : ℚ := (113169/13107200000000)

def plusWeights0807 : Fin 11 → ℚ := ![(113169/13107200000000), (113169/1310720000000), (1018521/2621440000000), (339507/327680000000), (2376549/1310720000000), (7129647/3276800000000), (2389349/1310720000000), (351987/327680000000), (1164057/2621440000000), (800671/6553600000000), (113169/6553600000000)]

def minusWeights0807 : Fin 11 → ℚ := ![(113169/13107200000000), (113169/1310720000000), (1018521/2621440000000), (339507/327680000000), (2376549/1310720000000), (7129647/3276800000000), (2363749/1310720000000), (327027/327680000000), (174597/524288000000), (331019/6553600000000), 0]

theorem checked0807 :
    (∀ i, 0 ≤ plusWeights0807 i) ∧
    (∀ i, 0 ≤ minusWeights0807 i) ∧
    (∀ i, plusCoefficients coefficients0807 upper0807 i = powerCoefficients10 plusWeights0807 i) ∧
    (∀ i, minusCoefficients coefficients0807 upper0807 i = powerCoefficients10 minusWeights0807 i) := by
  decide +kernel

theorem bound0807 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0807 g| ≤ (upper0807 : ℝ) :=
  abs_of_coefficients coefficients0807 upper0807 powerCoefficients10 plusWeights0807 minusWeights0807
    checked0807.1 checked0807.2.1 checked0807.2.2.1 checked0807.2.2.2
    (power_identity10 plusWeights0807) (power_identity10 minusWeights0807) g hg hmax

def envelope0807 : Envelope := ⟨coefficients0807, upper0807, bound0807⟩

def coefficients0808 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/512), (5/512), (35/4096), (25/8192), (125/131072)]

def upper0808 : ℚ := (113569/10485760000000)

def plusWeights0808 : Fin 11 → ℚ := ![(113569/10485760000000), (113569/1048576000000), (1022121/2097152000000), (340707/262144000000), (2384949/1048576000000), (7154847/2621440000000), (2395189/1048576000000), (351203/262144000000), (5756621/10485760000000), (788917/5242880000000), (113569/5242880000000)]

def minusWeights0808 : Fin 11 → ℚ := ![(113569/10485760000000), (113569/1048576000000), (1022121/2097152000000), (340707/262144000000), (2384949/1048576000000), (7154847/2621440000000), (2374709/1048576000000), (330211/262144000000), (4464589/10485760000000), (346773/5242880000000), 0]

theorem checked0808 :
    (∀ i, 0 ≤ plusWeights0808 i) ∧
    (∀ i, 0 ≤ minusWeights0808 i) ∧
    (∀ i, plusCoefficients coefficients0808 upper0808 i = powerCoefficients10 plusWeights0808 i) ∧
    (∀ i, minusCoefficients coefficients0808 upper0808 i = powerCoefficients10 minusWeights0808 i) := by
  decide +kernel

theorem bound0808 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0808 g| ≤ (upper0808 : ℝ) :=
  abs_of_coefficients coefficients0808 upper0808 powerCoefficients10 plusWeights0808 minusWeights0808
    checked0808.1 checked0808.2.1 checked0808.2.2.1 checked0808.2.2.2
    (power_identity10 plusWeights0808) (power_identity10 minusWeights0808) g hg hmax

def envelope0808 : Envelope := ⟨coefficients0808, upper0808, bound0808⟩

def coefficients0809 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (25/2048), (15/2048), (105/8192), (75/8192), (1675/524288)]

def upper0809 : ℚ := (2742467/209715200000000)

def plusWeights0809 : Fin 11 → ℚ := ![(2742467/209715200000000), (2742467/20971520000000), (24682203/41943040000000), (8227401/5242880000000), (57591807/20971520000000), (172775421/52428800000000), (57847807/20971520000000), (8487241/5242880000000), (27851739/41943040000000), (763623/4194304000000), (2742467/104857600000000)]

def minusWeights0809 : Fin 11 → ℚ := ![(2742467/209715200000000), (2742467/20971520000000), (24682203/41943040000000), (8227401/5242880000000), (57591807/20971520000000), (172775421/52428800000000), (57335807/20971520000000), (7967561/5242880000000), (21512667/41943040000000), (1666819/20971520000000), 0]

theorem checked0809 :
    (∀ i, 0 ≤ plusWeights0809 i) ∧
    (∀ i, 0 ≤ minusWeights0809 i) ∧
    (∀ i, plusCoefficients coefficients0809 upper0809 i = powerCoefficients10 plusWeights0809 i) ∧
    (∀ i, minusCoefficients coefficients0809 upper0809 i = powerCoefficients10 minusWeights0809 i) := by
  decide +kernel

theorem bound0809 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0809 g| ≤ (upper0809 : ℝ) :=
  abs_of_coefficients coefficients0809 upper0809 powerCoefficients10 plusWeights0809 minusWeights0809
    checked0809.1 checked0809.2.1 checked0809.2.2.1 checked0809.2.2.2
    (power_identity10 plusWeights0809) (power_identity10 minusWeights0809) g hg hmax

def envelope0809 : Envelope := ⟨coefficients0809, upper0809, bound0809⟩

def coefficients0810 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/2048), (-93/8192), (507/16384), (459/32768), (3615/524288)]

def upper0810 : ℚ := (12973491/1048576000000000)

def plusWeights0810 : Fin 11 → ℚ := ![(12973491/1048576000000000), (12973491/104857600000000), (116761419/209715200000000), (38920473/26214400000000), (272443311/104857600000000), (817329933/262144000000000), (273825711/104857600000000), (40273113/26214400000000), (1061607/1677721600000), (91061679/524288000000000), (12973491/524288000000000)]

def minusWeights0810 : Fin 11 → ℚ := ![(12973491/1048576000000000), (12973491/104857600000000), (116761419/209715200000000), (38920473/26214400000000), (272443311/104857600000000), (817329933/262144000000000), (271060911/104857600000000), (37567833/26214400000000), (100821963/209715200000000), (38673231/524288000000000), 0]

theorem checked0810 :
    (∀ i, 0 ≤ plusWeights0810 i) ∧
    (∀ i, 0 ≤ minusWeights0810 i) ∧
    (∀ i, plusCoefficients coefficients0810 upper0810 i = powerCoefficients10 plusWeights0810 i) ∧
    (∀ i, minusCoefficients coefficients0810 upper0810 i = powerCoefficients10 minusWeights0810 i) := by
  decide +kernel

theorem bound0810 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0810 g| ≤ (upper0810 : ℝ) :=
  abs_of_coefficients coefficients0810 upper0810 powerCoefficients10 plusWeights0810 minusWeights0810
    checked0810.1 checked0810.2.1 checked0810.2.2.1 checked0810.2.2.2
    (power_identity10 plusWeights0810) (power_identity10 minusWeights0810) g hg hmax

def envelope0810 : Envelope := ⟨coefficients0810, upper0810, bound0810⟩

def coefficients0811 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/2048), (-93/8192), (291/8192), (267/16384), (4365/524288)]

def upper0811 : ℚ := (13024041/1048576000000000)

def plusWeights0811 : Fin 11 → ℚ := ![(13024041/1048576000000000), (13024041/104857600000000), (117216369/209715200000000), (39072123/26214400000000), (273504861/104857600000000), (820514583/262144000000000), (274887261/104857600000000), (40424763/26214400000000), (5326617/8388608000000), (91363629/524288000000000), (13024041/524288000000000)]

def minusWeights0811 : Fin 11 → ℚ := ![(13024041/1048576000000000), (13024041/104857600000000), (117216369/209715200000000), (39072123/26214400000000), (273504861/104857600000000), (820514583/262144000000000), (272122461/104857600000000), (37719483/26214400000000), (101267313/209715200000000), (38876781/524288000000000), 0]

theorem checked0811 :
    (∀ i, 0 ≤ plusWeights0811 i) ∧
    (∀ i, 0 ≤ minusWeights0811 i) ∧
    (∀ i, plusCoefficients coefficients0811 upper0811 i = powerCoefficients10 plusWeights0811 i) ∧
    (∀ i, minusCoefficients coefficients0811 upper0811 i = powerCoefficients10 minusWeights0811 i) := by
  decide +kernel

theorem bound0811 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0811 g| ≤ (upper0811 : ℝ) :=
  abs_of_coefficients coefficients0811 upper0811 powerCoefficients10 plusWeights0811 minusWeights0811
    checked0811.1 checked0811.2.1 checked0811.2.2.1 checked0811.2.2.2
    (power_identity10 plusWeights0811) (power_identity10 minusWeights0811) g hg hmax

def envelope0811 : Envelope := ⟨coefficients0811, upper0811, bound0811⟩

def coefficients0812 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/2048), (-93/8192), (1419/32768), (1503/65536), (17835/524288)]

def upper0812 : ℚ := (2623059/209715200000000)

def plusWeights0812 : Fin 11 → ℚ := ![(2623059/209715200000000), (2623059/20971520000000), (23607531/41943040000000), (7869177/5242880000000), (55084239/20971520000000), (165252717/52428800000000), (55360719/20971520000000), (1627941/1048576000000), (134003031/209715200000000), (91904979/524288000000000), (2623059/104857600000000)]

def minusWeights0812 : Fin 11 → ℚ := ![(2623059/209715200000000), (2623059/20971520000000), (23607531/41943040000000), (7869177/5242880000000), (55084239/20971520000000), (165252717/52428800000000), (54807759/20971520000000), (7598649/5242880000000), (102072279/209715200000000), (39247971/524288000000000), 0]

theorem checked0812 :
    (∀ i, 0 ≤ plusWeights0812 i) ∧
    (∀ i, 0 ≤ minusWeights0812 i) ∧
    (∀ i, plusCoefficients coefficients0812 upper0812 i = powerCoefficients10 plusWeights0812 i) ∧
    (∀ i, minusCoefficients coefficients0812 upper0812 i = powerCoefficients10 minusWeights0812 i) := by
  decide +kernel

theorem bound0812 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0812 g| ≤ (upper0812 : ℝ) :=
  abs_of_coefficients coefficients0812 upper0812 powerCoefficients10 plusWeights0812 minusWeights0812
    checked0812.1 checked0812.2.1 checked0812.2.2.1 checked0812.2.2.2
    (power_identity10 plusWeights0812) (power_identity10 minusWeights0812) g hg hmax

def envelope0812 : Envelope := ⟨coefficients0812, upper0812, bound0812⟩

def coefficients0813 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/2048), (57/8192), (1149/32768), (1113/65536), (13605/524288)]

def upper0813 : ℚ := (14941809/1048576000000000)

def plusWeights0813 : Fin 11 → ℚ := ![(14941809/1048576000000000), (14941809/104857600000000), (134476281/209715200000000), (44825427/26214400000000), (313777989/104857600000000), (941333967/262144000000000), (315160389/104857600000000), (46226067/26214400000000), (151576377/209715200000000), (103828029/524288000000000), (14941809/524288000000000)]

def minusWeights0813 : Fin 11 → ℚ := ![(14941809/1048576000000000), (14941809/104857600000000), (134476281/209715200000000), (44825427/26214400000000), (313777989/104857600000000), (941333967/262144000000000), (312395589/104857600000000), (43424787/26214400000000), (23475237/41943040000000), (45590061/524288000000000), 0]

theorem checked0813 :
    (∀ i, 0 ≤ plusWeights0813 i) ∧
    (∀ i, 0 ≤ minusWeights0813 i) ∧
    (∀ i, plusCoefficients coefficients0813 upper0813 i = powerCoefficients10 plusWeights0813 i) ∧
    (∀ i, minusCoefficients coefficients0813 upper0813 i = powerCoefficients10 minusWeights0813 i) := by
  decide +kernel

theorem bound0813 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0813 g| ≤ (upper0813 : ℝ) :=
  abs_of_coefficients coefficients0813 upper0813 powerCoefficients10 plusWeights0813 minusWeights0813
    checked0813.1 checked0813.2.1 checked0813.2.2.1 checked0813.2.2.2
    (power_identity10 plusWeights0813) (power_identity10 minusWeights0813) g hg hmax

def envelope0813 : Envelope := ⟨coefficients0813, upper0813, bound0813⟩

def coefficients0814 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/512), (163/8192), (21/2048), (1/128), (15/8192)]

def upper0814 : ℚ := (258411/16384000000000)

def plusWeights0814 : Fin 11 → ℚ := ![(258411/16384000000000), (258411/1638400000000), (2325699/3276800000000), (775233/409600000000), (5426631/1638400000000), (16279893/4096000000000), (5449031/1638400000000), (49903/25600000000), (522879/655360000000), (1790699/8192000000000), (258411/8192000000000)]

def minusWeights0814 : Fin 11 → ℚ := ![(258411/16384000000000), (258411/1638400000000), (2325699/3276800000000), (775233/409600000000), (5426631/1638400000000), (16279893/4096000000000), (5404231/1638400000000), (376009/204800000000), (2037003/3276800000000), (793411/8192000000000), 0]

theorem checked0814 :
    (∀ i, 0 ≤ plusWeights0814 i) ∧
    (∀ i, 0 ≤ minusWeights0814 i) ∧
    (∀ i, plusCoefficients coefficients0814 upper0814 i = powerCoefficients10 plusWeights0814 i) ∧
    (∀ i, minusCoefficients coefficients0814 upper0814 i = powerCoefficients10 minusWeights0814 i) := by
  decide +kernel

theorem bound0814 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0814 g| ≤ (upper0814 : ℝ) :=
  abs_of_coefficients coefficients0814 upper0814 powerCoefficients10 plusWeights0814 minusWeights0814
    checked0814.1 checked0814.2.1 checked0814.2.2.1 checked0814.2.2.2
    (power_identity10 plusWeights0814) (power_identity10 minusWeights0814) g hg hmax

def envelope0814 : Envelope := ⟨coefficients0814, upper0814, bound0814⟩

def coefficients0815 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (-51/2048), (-69/2048), (-2199/65536), (-1623/131072)]

def upper0815 : ℚ := (15448797/1310720000000000)

def plusWeights0815 : Fin 11 → ℚ := ![(15448797/1310720000000000), (15448797/131072000000000), (139039173/262144000000000), (46346391/32768000000000), (324424737/131072000000000), (973274211/327680000000000), (326344737/131072000000000), (48184791/32768000000000), (160032453/262144000000000), (22056879/131072000000000), (15448797/655360000000000)]

def minusWeights0815 : Fin 11 → ℚ := ![(15448797/1310720000000000), (15448797/131072000000000), (139039173/262144000000000), (46346391/32768000000000), (324424737/131072000000000), (973274211/327680000000000), (322504737/131072000000000), (44507991/32768000000000), (118045893/262144000000000), (1768143/26214400000000), 0]

theorem checked0815 :
    (∀ i, 0 ≤ plusWeights0815 i) ∧
    (∀ i, 0 ≤ minusWeights0815 i) ∧
    (∀ i, plusCoefficients coefficients0815 upper0815 i = powerCoefficients10 plusWeights0815 i) ∧
    (∀ i, minusCoefficients coefficients0815 upper0815 i = powerCoefficients10 minusWeights0815 i) := by
  decide +kernel

theorem bound0815 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0815 g| ≤ (upper0815 : ℝ) :=
  abs_of_coefficients coefficients0815 upper0815 powerCoefficients10 plusWeights0815 minusWeights0815
    checked0815.1 checked0815.2.1 checked0815.2.2.1 checked0815.2.2.2
    (power_identity10 plusWeights0815) (power_identity10 minusWeights0815) g hg hmax

def envelope0815 : Envelope := ⟨coefficients0815, upper0815, bound0815⟩

def coefficients0816 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (-75/4096), (-105/4096), (-945/65536), (-525/131072)]

def upper0816 : ℚ := (657783/52428800000000)

def plusWeights0816 : Fin 11 → ℚ := ![(657783/52428800000000), (657783/5242880000000), (5920047/10485760000000), (1973349/1310720000000), (13813443/5242880000000), (41440329/13107200000000), (13890243/5242880000000), (2047749/1310720000000), (6781359/10485760000000), (4667097/26214400000000), (657783/26214400000000)]

def minusWeights0816 : Fin 11 → ℚ := ![(657783/52428800000000), (657783/5242880000000), (5920047/10485760000000), (1973349/1310720000000), (13813443/5242880000000), (41440329/13107200000000), (13736643/5242880000000), (1898949/1310720000000), (1011747/2097152000000), (1910733/26214400000000), 0]

theorem checked0816 :
    (∀ i, 0 ≤ plusWeights0816 i) ∧
    (∀ i, 0 ≤ minusWeights0816 i) ∧
    (∀ i, plusCoefficients coefficients0816 upper0816 i = powerCoefficients10 plusWeights0816 i) ∧
    (∀ i, minusCoefficients coefficients0816 upper0816 i = powerCoefficients10 minusWeights0816 i) := by
  decide +kernel

theorem bound0816 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0816 g| ≤ (upper0816 : ℝ) :=
  abs_of_coefficients coefficients0816 upper0816 powerCoefficients10 plusWeights0816 minusWeights0816
    checked0816.1 checked0816.2.1 checked0816.2.2.1 checked0816.2.2.2
    (power_identity10 plusWeights0816) (power_identity10 minusWeights0816) g hg hmax

def envelope0816 : Envelope := ⟨coefficients0816, upper0816, bound0816⟩

def coefficients0817 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (-65/4096), (-95/4096), (-855/65536), (-475/131072)]

def upper0817 : ℚ := (671937/52428800000000)

def plusWeights0817 : Fin 11 → ℚ := ![(671937/52428800000000), (671937/5242880000000), (6047433/10485760000000), (2015811/1310720000000), (14110677/5242880000000), (42332031/13107200000000), (14187477/5242880000000), (2090531/1310720000000), (6916681/10485760000000), (4758383/26214400000000), (671937/26214400000000)]

def minusWeights0817 : Fin 11 → ℚ := ![(671937/52428800000000), (671937/5242880000000), (6047433/10485760000000), (2015811/1310720000000), (14110677/5242880000000), (42332031/13107200000000), (14033877/5242880000000), (1941091/1310720000000), (1035637/2097152000000), (1960987/26214400000000), 0]

theorem checked0817 :
    (∀ i, 0 ≤ plusWeights0817 i) ∧
    (∀ i, 0 ≤ minusWeights0817 i) ∧
    (∀ i, plusCoefficients coefficients0817 upper0817 i = powerCoefficients10 plusWeights0817 i) ∧
    (∀ i, minusCoefficients coefficients0817 upper0817 i = powerCoefficients10 minusWeights0817 i) := by
  decide +kernel

theorem bound0817 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0817 g| ≤ (upper0817 : ℝ) :=
  abs_of_coefficients coefficients0817 upper0817 powerCoefficients10 plusWeights0817 minusWeights0817
    checked0817.1 checked0817.2.1 checked0817.2.2.1 checked0817.2.2.2
    (power_identity10 plusWeights0817) (power_identity10 minusWeights0817) g hg hmax

def envelope0817 : Envelope := ⟨coefficients0817, upper0817, bound0817⟩

def coefficients0818 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (-15/4096), (-45/4096), (-405/65536), (-225/131072)]

def upper0818 : ℚ := (742707/52428800000000)

def plusWeights0818 : Fin 11 → ℚ := ![(742707/52428800000000), (742707/5242880000000), (6684363/10485760000000), (2228121/1310720000000), (15596847/5242880000000), (46790541/13107200000000), (15673647/5242880000000), (2304441/1310720000000), (7593291/10485760000000), (5214813/26214400000000), (742707/26214400000000)]

def minusWeights0818 : Fin 11 → ℚ := ![(742707/52428800000000), (742707/5242880000000), (6684363/10485760000000), (2228121/1310720000000), (15596847/5242880000000), (46790541/13107200000000), (15520047/5242880000000), (2151801/1310720000000), (1155087/2097152000000), (2212257/26214400000000), 0]

theorem checked0818 :
    (∀ i, 0 ≤ plusWeights0818 i) ∧
    (∀ i, 0 ≤ minusWeights0818 i) ∧
    (∀ i, plusCoefficients coefficients0818 upper0818 i = powerCoefficients10 plusWeights0818 i) ∧
    (∀ i, minusCoefficients coefficients0818 upper0818 i = powerCoefficients10 minusWeights0818 i) := by
  decide +kernel

theorem bound0818 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0818 g| ≤ (upper0818 : ℝ) :=
  abs_of_coefficients coefficients0818 upper0818 powerCoefficients10 plusWeights0818 minusWeights0818
    checked0818.1 checked0818.2.1 checked0818.2.2.1 checked0818.2.2.2
    (power_identity10 plusWeights0818) (power_identity10 minusWeights0818) g hg hmax

def envelope0818 : Envelope := ⟨coefficients0818, upper0818, bound0818⟩

def coefficients0819 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (5/512), (415/32768), (575/65536), (1425/524288)]

def upper0819 : ℚ := (3305257/209715200000000)

def plusWeights0819 : Fin 11 → ℚ := ![(3305257/209715200000000), (3305257/20971520000000), (29747313/41943040000000), (9915771/5242880000000), (69410397/20971520000000), (208231191/52428800000000), (69717597/20971520000000), (10228091/5242880000000), (6712381/8388608000000), (4600993/20971520000000), (3305257/104857600000000)]

def minusWeights0819 : Fin 11 → ℚ := ![(3305257/209715200000000), (3305257/20971520000000), (29747313/41943040000000), (9915771/5242880000000), (69410397/20971520000000), (208231191/52428800000000), (69103197/20971520000000), (9603451/5242880000000), (25932721/41943040000000), (2009521/20971520000000), 0]

theorem checked0819 :
    (∀ i, 0 ≤ plusWeights0819 i) ∧
    (∀ i, 0 ≤ minusWeights0819 i) ∧
    (∀ i, plusCoefficients coefficients0819 upper0819 i = powerCoefficients10 plusWeights0819 i) ∧
    (∀ i, minusCoefficients coefficients0819 upper0819 i = powerCoefficients10 minusWeights0819 i) := by
  decide +kernel

theorem bound0819 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0819 g| ≤ (upper0819 : ℝ) :=
  abs_of_coefficients coefficients0819 upper0819 powerCoefficients10 plusWeights0819 minusWeights0819
    checked0819.1 checked0819.2.1 checked0819.2.2.1 checked0819.2.2.2
    (power_identity10 plusWeights0819) (power_identity10 minusWeights0819) g hg hmax

def envelope0819 : Envelope := ⟨coefficients0819, upper0819, bound0819⟩

def coefficients0820 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (5/512), (1075/32768), (1595/65536), (11865/524288)]

def upper0820 : ℚ := (16755893/1048576000000000)

def plusWeights0820 : Fin 11 → ℚ := ![(16755893/1048576000000000), (16755893/104857600000000), (150803037/209715200000000), (50267679/26214400000000), (351873753/104857600000000), (1055621259/262144000000000), (353409753/104857600000000), (51829279/26214400000000), (169918237/209715200000000), (4655689/20971520000000), (16755893/524288000000000)]

def minusWeights0820 : Fin 11 → ℚ := ![(16755893/1048576000000000), (16755893/104857600000000), (150803037/209715200000000), (50267679/26214400000000), (351873753/104857600000000), (1055621259/262144000000000), (350337753/104857600000000), (48706079/26214400000000), (131687837/209715200000000), (10233341/104857600000000), 0]

theorem checked0820 :
    (∀ i, 0 ≤ plusWeights0820 i) ∧
    (∀ i, 0 ≤ minusWeights0820 i) ∧
    (∀ i, plusCoefficients coefficients0820 upper0820 i = powerCoefficients10 plusWeights0820 i) ∧
    (∀ i, minusCoefficients coefficients0820 upper0820 i = powerCoefficients10 minusWeights0820 i) := by
  decide +kernel

theorem bound0820 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0820 g| ≤ (upper0820 : ℝ) :=
  abs_of_coefficients coefficients0820 upper0820 powerCoefficients10 plusWeights0820 minusWeights0820
    checked0820.1 checked0820.2.1 checked0820.2.2.1 checked0820.2.2.2
    (power_identity10 plusWeights0820) (power_identity10 minusWeights0820) g hg hmax

def envelope0820 : Envelope := ⟨coefficients0820, upper0820, bound0820⟩

def coefficients0821 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (5/512), (1225/32768), (1745/65536), (13365/524288)]

def upper0821 : ℚ := (16806593/1048576000000000)

def plusWeights0821 : Fin 11 → ℚ := ![(16806593/1048576000000000), (16806593/104857600000000), (151259337/209715200000000), (50419779/26214400000000), (352938453/104857600000000), (1058815359/262144000000000), (354474453/104857600000000), (51981379/26214400000000), (170384137/209715200000000), (4667797/20971520000000), (16806593/524288000000000)]

def minusWeights0821 : Fin 11 → ℚ := ![(16806593/1048576000000000), (16806593/104857600000000), (151259337/209715200000000), (50419779/26214400000000), (352938453/104857600000000), (1058815359/262144000000000), (351402453/104857600000000), (48858179/26214400000000), (132134537/209715200000000), (10274201/104857600000000), 0]

theorem checked0821 :
    (∀ i, 0 ≤ plusWeights0821 i) ∧
    (∀ i, 0 ≤ minusWeights0821 i) ∧
    (∀ i, plusCoefficients coefficients0821 upper0821 i = powerCoefficients10 plusWeights0821 i) ∧
    (∀ i, minusCoefficients coefficients0821 upper0821 i = powerCoefficients10 minusWeights0821 i) := by
  decide +kernel

theorem bound0821 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0821 g| ≤ (upper0821 : ℝ) :=
  abs_of_coefficients coefficients0821 upper0821 powerCoefficients10 plusWeights0821 minusWeights0821
    checked0821.1 checked0821.2.1 checked0821.2.2.1 checked0821.2.2.2
    (power_identity10 plusWeights0821) (power_identity10 minusWeights0821) g hg hmax

def envelope0821 : Envelope := ⟨coefficients0821, upper0821, bound0821⟩

def coefficients0822 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (15/1024), (105/8192), (75/16384), (375/262144)]

def upper0822 : ℚ := (340707/20971520000000)

def plusWeights0822 : Fin 11 → ℚ := ![(340707/20971520000000), (340707/2097152000000), (3066363/4194304000000), (1022121/524288000000), (7154847/2097152000000), (21464541/5242880000000), (7185567/2097152000000), (1053609/524288000000), (17269863/20971520000000), (2366751/10485760000000), (340707/10485760000000)]

def minusWeights0822 : Fin 11 → ℚ := ![(340707/20971520000000), (340707/2097152000000), (3066363/4194304000000), (1022121/524288000000), (7154847/2097152000000), (21464541/5242880000000), (7124127/2097152000000), (990633/524288000000), (13393767/20971520000000), (1040319/10485760000000), 0]

theorem checked0822 :
    (∀ i, 0 ≤ plusWeights0822 i) ∧
    (∀ i, 0 ≤ minusWeights0822 i) ∧
    (∀ i, plusCoefficients coefficients0822 upper0822 i = powerCoefficients10 plusWeights0822 i) ∧
    (∀ i, minusCoefficients coefficients0822 upper0822 i = powerCoefficients10 minusWeights0822 i) := by
  decide +kernel

theorem bound0822 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0822 g| ≤ (upper0822 : ℝ) :=
  abs_of_coefficients coefficients0822 upper0822 powerCoefficients10 plusWeights0822 minusWeights0822
    checked0822.1 checked0822.2.1 checked0822.2.2.1 checked0822.2.2.2
    (power_identity10 plusWeights0822) (power_identity10 minusWeights0822) g hg hmax

def envelope0822 : Envelope := ⟨coefficients0822, upper0822, bound0822⟩

def coefficients0823 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/64), (3/128), (37/1024), (27/1024), (25/4096)]

def upper0823 : ℚ := (150381/8192000000000)

def plusWeights0823 : Fin 11 → ℚ := ![(150381/8192000000000), (150381/819200000000), (1353429/1638400000000), (451143/204800000000), (3158001/819200000000), (9474003/2048000000000), (3170801/819200000000), (464423/204800000000), (1519141/1638400000000), (1039773/4096000000000), (150381/4096000000000)]

def minusWeights0823 : Fin 11 → ℚ := ![(150381/8192000000000), (150381/819200000000), (1353429/1638400000000), (451143/204800000000), (3158001/819200000000), (9474003/2048000000000), (3145201/819200000000), (437863/204800000000), (1187717/1638400000000), (464037/4096000000000), 0]

theorem checked0823 :
    (∀ i, 0 ≤ plusWeights0823 i) ∧
    (∀ i, 0 ≤ minusWeights0823 i) ∧
    (∀ i, plusCoefficients coefficients0823 upper0823 i = powerCoefficients10 plusWeights0823 i) ∧
    (∀ i, minusCoefficients coefficients0823 upper0823 i = powerCoefficients10 minusWeights0823 i) := by
  decide +kernel

theorem bound0823 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0823 g| ≤ (upper0823 : ℝ) :=
  abs_of_coefficients coefficients0823 upper0823 powerCoefficients10 plusWeights0823 minusWeights0823
    checked0823.1 checked0823.2.1 checked0823.2.2.1 checked0823.2.2.2
    (power_identity10 plusWeights0823) (power_identity10 minusWeights0823) g hg hmax

def envelope0823 : Envelope := ⟨coefficients0823, upper0823, bound0823⟩

def coefficients0824 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/64), (3/128), (21/512), (1/32), (15/2048)]

def upper0824 : ℚ := (75411/4096000000000)

def plusWeights0824 : Fin 11 → ℚ := ![(75411/4096000000000), (75411/409600000000), (678699/819200000000), (226233/102400000000), (1583631/409600000000), (4750893/1024000000000), (1590031/409600000000), (232873/102400000000), (152319/163840000000), (521199/2048000000000), (75411/2048000000000)]

def minusWeights0824 : Fin 11 → ℚ := ![(75411/4096000000000), (75411/409600000000), (678699/819200000000), (226233/102400000000), (1583631/409600000000), (4750893/1024000000000), (1577231/409600000000), (219593/102400000000), (595803/819200000000), (232911/2048000000000), 0]

theorem checked0824 :
    (∀ i, 0 ≤ plusWeights0824 i) ∧
    (∀ i, 0 ≤ minusWeights0824 i) ∧
    (∀ i, plusCoefficients coefficients0824 upper0824 i = powerCoefficients10 plusWeights0824 i) ∧
    (∀ i, minusCoefficients coefficients0824 upper0824 i = powerCoefficients10 minusWeights0824 i) := by
  decide +kernel

theorem bound0824 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0824 g| ≤ (upper0824 : ℝ) :=
  abs_of_coefficients coefficients0824 upper0824 powerCoefficients10 plusWeights0824 minusWeights0824
    checked0824.1 checked0824.2.1 checked0824.2.2.1 checked0824.2.2.2
    (power_identity10 plusWeights0824) (power_identity10 minusWeights0824) g hg hmax

def envelope0824 : Envelope := ⟨coefficients0824, upper0824, bound0824⟩

def coefficients0825 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (35/2048), (5/2048), (175/8192), (175/8192), (4025/524288)]

def upper0825 : ℚ := (3684641/209715200000000)

def plusWeights0825 : Fin 11 → ℚ := ![(3684641/209715200000000), (3684641/20971520000000), (33161769/41943040000000), (11053923/5242880000000), (77377461/20971520000000), (232132383/52428800000000), (77735861/20971520000000), (11413603/5242880000000), (37502249/41943040000000), (5143009/20971520000000), (3684641/104857600000000)]

def minusWeights0825 : Fin 11 → ℚ := ![(3684641/209715200000000), (3684641/20971520000000), (33161769/41943040000000), (11053923/5242880000000), (77377461/20971520000000), (232132383/52428800000000), (77019061/20971520000000), (10694243/5242880000000), (28821289/41943040000000), (2226273/20971520000000), 0]

theorem checked0825 :
    (∀ i, 0 ≤ plusWeights0825 i) ∧
    (∀ i, 0 ≤ minusWeights0825 i) ∧
    (∀ i, plusCoefficients coefficients0825 upper0825 i = powerCoefficients10 plusWeights0825 i) ∧
    (∀ i, minusCoefficients coefficients0825 upper0825 i = powerCoefficients10 minusWeights0825 i) := by
  decide +kernel

theorem bound0825 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0825 g| ≤ (upper0825 : ℝ) :=
  abs_of_coefficients coefficients0825 upper0825 powerCoefficients10 plusWeights0825 minusWeights0825
    checked0825.1 checked0825.2.1 checked0825.2.2.1 checked0825.2.2.2
    (power_identity10 plusWeights0825) (power_identity10 minusWeights0825) g hg hmax

def envelope0825 : Envelope := ⟨coefficients0825, upper0825, bound0825⟩

def coefficients0826 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/512), (13/4096), (751/16384), (687/32768), (2785/262144)]

def upper0826 : ℚ := (9634269/524288000000000)

def plusWeights0826 : Fin 11 → ℚ := ![(9634269/524288000000000), (9634269/52428800000000), (86708421/104857600000000), (28902807/13107200000000), (202319649/52428800000000), (606958947/131072000000000), (203241249/52428800000000), (29828567/13107200000000), (3916621/4194304000000), (67098761/262144000000000), (9634269/262144000000000)]

def minusWeights0826 : Fin 11 → ℚ := ![(9634269/524288000000000), (9634269/52428800000000), (86708421/104857600000000), (28902807/13107200000000), (202319649/52428800000000), (606958947/131072000000000), (201398049/52428800000000), (27977047/13107200000000), (75501317/104857600000000), (29243929/262144000000000), 0]

theorem checked0826 :
    (∀ i, 0 ≤ plusWeights0826 i) ∧
    (∀ i, 0 ≤ minusWeights0826 i) ∧
    (∀ i, plusCoefficients coefficients0826 upper0826 i = powerCoefficients10 plusWeights0826 i) ∧
    (∀ i, minusCoefficients coefficients0826 upper0826 i = powerCoefficients10 minusWeights0826 i) := by
  decide +kernel

theorem bound0826 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0826 g| ≤ (upper0826 : ℝ) :=
  abs_of_coefficients coefficients0826 upper0826 powerCoefficients10 plusWeights0826 minusWeights0826
    checked0826.1 checked0826.2.1 checked0826.2.2.1 checked0826.2.2.2
    (power_identity10 plusWeights0826) (power_identity10 minusWeights0826) g hg hmax

def envelope0826 : Envelope := ⟨coefficients0826, upper0826, bound0826⟩

def coefficients0827 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/512), (131/8192), (83/8192), (93/8192), (95/32768)]

def upper0827 : ℚ := (1264203/65536000000000)

def plusWeights0827 : Fin 11 → ℚ := ![(1264203/65536000000000), (1264203/6553600000000), (11377827/13107200000000), (3792609/1638400000000), (26548263/6553600000000), (79644789/16384000000000), (26663463/6553600000000), (3910429/1638400000000), (2564887/2621440000000), (8789227/32768000000000), (1264203/32768000000000)]

def minusWeights0827 : Fin 11 → ℚ := ![(1264203/65536000000000), (1264203/6553600000000), (11377827/13107200000000), (3792609/1638400000000), (26548263/6553600000000), (79644789/16384000000000), (26433063/6553600000000), (3674789/1638400000000), (9931219/13107200000000), (3852803/32768000000000), 0]

theorem checked0827 :
    (∀ i, 0 ≤ plusWeights0827 i) ∧
    (∀ i, 0 ≤ minusWeights0827 i) ∧
    (∀ i, plusCoefficients coefficients0827 upper0827 i = powerCoefficients10 plusWeights0827 i) ∧
    (∀ i, minusCoefficients coefficients0827 upper0827 i = powerCoefficients10 minusWeights0827 i) := by
  decide +kernel

theorem bound0827 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0827 g| ≤ (upper0827 : ℝ) :=
  abs_of_coefficients coefficients0827 upper0827 powerCoefficients10 plusWeights0827 minusWeights0827
    checked0827.1 checked0827.2.1 checked0827.2.2.1 checked0827.2.2.2
    (power_identity10 plusWeights0827) (power_identity10 minusWeights0827) g hg hmax

def envelope0827 : Envelope := ⟨coefficients0827, upper0827, bound0827⟩

def coefficients0828 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/1024), (207/8192), (39/2048), (63/4096), (15/4096)]

def upper0828 : ℚ := (190389/8192000000000)

def plusWeights0828 : Fin 11 → ℚ := ![(190389/8192000000000), (190389/819200000000), (1713501/1638400000000), (571167/204800000000), (3998169/819200000000), (11994507/2048000000000), (4014969/819200000000), (1176969/409600000000), (1927833/1638400000000), (660309/2048000000000), (190389/4096000000000)]

def minusWeights0828 : Fin 11 → ℚ := ![(190389/8192000000000), (190389/819200000000), (1713501/1638400000000), (571167/204800000000), (3998169/819200000000), (11994507/2048000000000), (3981369/819200000000), (1107699/409600000000), (1499169/1638400000000), (72909/512000000000), 0]

theorem checked0828 :
    (∀ i, 0 ≤ plusWeights0828 i) ∧
    (∀ i, 0 ≤ minusWeights0828 i) ∧
    (∀ i, plusCoefficients coefficients0828 upper0828 i = powerCoefficients10 plusWeights0828 i) ∧
    (∀ i, minusCoefficients coefficients0828 upper0828 i = powerCoefficients10 minusWeights0828 i) := by
  decide +kernel

theorem bound0828 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0828 g| ≤ (upper0828 : ℝ) :=
  abs_of_coefficients coefficients0828 upper0828 powerCoefficients10 plusWeights0828 minusWeights0828
    checked0828.1 checked0828.2.1 checked0828.2.2.1 checked0828.2.2.2
    (power_identity10 plusWeights0828) (power_identity10 minusWeights0828) g hg hmax

def envelope0828 : Envelope := ⟨coefficients0828, upper0828, bound0828⟩

def coefficients0829 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/1024), (357/8192), (63/4096), (3/256), (45/16384)]

def upper0829 : ℚ := (820233/32768000000000)

def plusWeights0829 : Fin 11 → ℚ := ![(820233/32768000000000), (820233/3276800000000), (7382097/6553600000000), (2460699/819200000000), (17224893/3276800000000), (51674679/8192000000000), (17292093/3276800000000), (2531469/819200000000), (1655037/1310720000000), (5664597/16384000000000), (820233/16384000000000)]

def minusWeights0829 : Fin 11 → ℚ := ![(820233/32768000000000), (820233/3276800000000), (7382097/6553600000000), (2460699/819200000000), (17224893/3276800000000), (51674679/8192000000000), (17157693/3276800000000), (2389929/819200000000), (6489009/6553600000000), (2537733/16384000000000), 0]

theorem checked0829 :
    (∀ i, 0 ≤ plusWeights0829 i) ∧
    (∀ i, 0 ≤ minusWeights0829 i) ∧
    (∀ i, plusCoefficients coefficients0829 upper0829 i = powerCoefficients10 plusWeights0829 i) ∧
    (∀ i, minusCoefficients coefficients0829 upper0829 i = powerCoefficients10 minusWeights0829 i) := by
  decide +kernel

theorem bound0829 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0829 g| ≤ (upper0829 : ℝ) :=
  abs_of_coefficients coefficients0829 upper0829 powerCoefficients10 plusWeights0829 minusWeights0829
    checked0829.1 checked0829.2.1 checked0829.2.2.1 checked0829.2.2.2
    (power_identity10 plusWeights0829) (power_identity10 minusWeights0829) g hg hmax

def envelope0829 : Envelope := ⟨coefficients0829, upper0829, bound0829⟩

def coefficients0830 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/1024), (357/8192), (27/1024), (93/4096), (45/8192)]

def upper0830 : ℚ := (412101/16384000000000)

def plusWeights0830 : Fin 11 → ℚ := ![(412101/16384000000000), (412101/1638400000000), (3708909/3276800000000), (1236303/409600000000), (8654121/1638400000000), (25962363/4096000000000), (8687721/1638400000000), (158961/51200000000), (4155813/3276800000000), (2844111/8192000000000), (412101/8192000000000)]

def minusWeights0830 : Fin 11 → ℚ := ![(412101/16384000000000), (412101/1638400000000), (3708909/3276800000000), (1236303/409600000000), (8654121/1638400000000), (25962363/4096000000000), (8620521/1638400000000), (600459/204800000000), (652401/655360000000), (1276899/8192000000000), 0]

theorem checked0830 :
    (∀ i, 0 ≤ plusWeights0830 i) ∧
    (∀ i, 0 ≤ minusWeights0830 i) ∧
    (∀ i, plusCoefficients coefficients0830 upper0830 i = powerCoefficients10 plusWeights0830 i) ∧
    (∀ i, minusCoefficients coefficients0830 upper0830 i = powerCoefficients10 minusWeights0830 i) := by
  decide +kernel

theorem bound0830 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0830 g| ≤ (upper0830 : ℝ) :=
  abs_of_coefficients coefficients0830 upper0830 powerCoefficients10 plusWeights0830 minusWeights0830
    checked0830.1 checked0830.2.1 checked0830.2.2.1 checked0830.2.2.2
    (power_identity10 plusWeights0830) (power_identity10 minusWeights0830) g hg hmax

def envelope0830 : Envelope := ⟨coefficients0830, upper0830, bound0830⟩

def coefficients0831 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/2048), (15/2048), (105/4096), (375/16384), (4275/524288)]

def upper0831 : ℚ := (4820331/209715200000000)

def plusWeights0831 : Fin 11 → ℚ := ![(4820331/209715200000000), (4820331/20971520000000), (43382979/41943040000000), (14460993/5242880000000), (101226951/20971520000000), (303680853/52428800000000), (101687751/20971520000000), (14925633/5242880000000), (49015491/41943040000000), (6720843/20971520000000), (4820331/104857600000000)]

def minusWeights0831 : Fin 11 → ℚ := ![(4820331/209715200000000), (4820331/20971520000000), (43382979/41943040000000), (14460993/5242880000000), (101226951/20971520000000), (303680853/52428800000000), (100766151/20971520000000), (13996353/5242880000000), (37750467/41943040000000), (2919819/20971520000000), 0]

theorem checked0831 :
    (∀ i, 0 ≤ plusWeights0831 i) ∧
    (∀ i, 0 ≤ minusWeights0831 i) ∧
    (∀ i, plusCoefficients coefficients0831 upper0831 i = powerCoefficients10 plusWeights0831 i) ∧
    (∀ i, minusCoefficients coefficients0831 upper0831 i = powerCoefficients10 minusWeights0831 i) := by
  decide +kernel

theorem bound0831 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0831 g| ≤ (upper0831 : ℝ) :=
  abs_of_coefficients coefficients0831 upper0831 powerCoefficients10 plusWeights0831 minusWeights0831
    checked0831.1 checked0831.2.1 checked0831.2.2.1 checked0831.2.2.2
    (power_identity10 plusWeights0831) (power_identity10 minusWeights0831) g hg hmax

def envelope0831 : Envelope := ⟨coefficients0831, upper0831, bound0831⟩

end BilayerDressed.CubicQuarticEnvelopes

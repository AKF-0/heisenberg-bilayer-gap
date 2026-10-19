import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0672 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-105/8192), (-15/4096), (-705/32768), (-675/65536)]

def upper0672 : ℚ := (35151/26214400000000)

def plusWeights0672 : Fin 11 → ℚ := ![(35151/26214400000000), (35151/2621440000000), (316359/5242880000000), (105453/655360000000), (738171/2621440000000), (2214513/6553600000000), (738171/2621440000000), (104613/655360000000), (296007/5242880000000), (124113/13107200000000), 0]

def minusWeights0672 : Fin 11 → ℚ := ![(35151/26214400000000), (35151/2621440000000), (316359/5242880000000), (105453/655360000000), (738171/2621440000000), (2214513/6553600000000), (738171/2621440000000), (106293/655360000000), (336711/5242880000000), (227397/13107200000000), (35151/13107200000000)]

theorem checked0672 :
    (∀ i, 0 ≤ plusWeights0672 i) ∧
    (∀ i, 0 ≤ minusWeights0672 i) ∧
    (∀ i, plusCoefficients coefficients0672 upper0672 i = powerCoefficients10 plusWeights0672 i) ∧
    (∀ i, minusCoefficients coefficients0672 upper0672 i = powerCoefficients10 minusWeights0672 i) := by
  decide +kernel

theorem bound0672 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0672 g| ≤ (upper0672 : ℝ) :=
  abs_of_coefficients coefficients0672 upper0672 powerCoefficients10 plusWeights0672 minusWeights0672
    checked0672.1 checked0672.2.1 checked0672.2.2.1 checked0672.2.2.2
    (power_identity10 plusWeights0672) (power_identity10 minusWeights0672) g hg hmax

def envelope0672 : Envelope := ⟨coefficients0672, upper0672, bound0672⟩

def coefficients0673 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-105/8192), (-15/4096), (-355/32768), (-325/65536)]

def upper0673 : ℚ := (34857/26214400000000)

def plusWeights0673 : Fin 11 → ℚ := ![(34857/26214400000000), (34857/2621440000000), (313713/5242880000000), (104571/655360000000), (731997/2621440000000), (2195991/6553600000000), (731997/2621440000000), (103731/655360000000), (293361/5242880000000), (122783/13107200000000), 0]

def minusWeights0673 : Fin 11 → ℚ := ![(34857/26214400000000), (34857/2621440000000), (313713/5242880000000), (104571/655360000000), (731997/2621440000000), (2195991/6553600000000), (731997/2621440000000), (105411/655360000000), (66813/1048576000000), (225787/13107200000000), (34857/13107200000000)]

theorem checked0673 :
    (∀ i, 0 ≤ plusWeights0673 i) ∧
    (∀ i, 0 ≤ minusWeights0673 i) ∧
    (∀ i, plusCoefficients coefficients0673 upper0673 i = powerCoefficients10 plusWeights0673 i) ∧
    (∀ i, minusCoefficients coefficients0673 upper0673 i = powerCoefficients10 minusWeights0673 i) := by
  decide +kernel

theorem bound0673 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0673 g| ≤ (upper0673 : ℝ) :=
  abs_of_coefficients coefficients0673 upper0673 powerCoefficients10 plusWeights0673 minusWeights0673
    checked0673.1 checked0673.2.1 checked0673.2.2.1 checked0673.2.2.2
    (power_identity10 plusWeights0673) (power_identity10 minusWeights0673) g hg hmax

def envelope0673 : Envelope := ⟨coefficients0673, upper0673, bound0673⟩

def coefficients0674 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-105/8192), (-15/4096), (-255/32768), (-225/65536)]

def upper0674 : ℚ := (34773/26214400000000)

def plusWeights0674 : Fin 11 → ℚ := ![(34773/26214400000000), (34773/2621440000000), (312957/5242880000000), (104319/655360000000), (730233/2621440000000), (2190699/6553600000000), (730233/2621440000000), (103479/655360000000), (58521/1048576000000), (122403/13107200000000), 0]

def minusWeights0674 : Fin 11 → ℚ := ![(34773/26214400000000), (34773/2621440000000), (312957/5242880000000), (104319/655360000000), (730233/2621440000000), (2190699/6553600000000), (730233/2621440000000), (105159/655360000000), (333309/5242880000000), (225327/13107200000000), (34773/13107200000000)]

theorem checked0674 :
    (∀ i, 0 ≤ plusWeights0674 i) ∧
    (∀ i, 0 ≤ minusWeights0674 i) ∧
    (∀ i, plusCoefficients coefficients0674 upper0674 i = powerCoefficients10 plusWeights0674 i) ∧
    (∀ i, minusCoefficients coefficients0674 upper0674 i = powerCoefficients10 minusWeights0674 i) := by
  decide +kernel

theorem bound0674 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0674 g| ≤ (upper0674 : ℝ) :=
  abs_of_coefficients coefficients0674 upper0674 powerCoefficients10 plusWeights0674 minusWeights0674
    checked0674.1 checked0674.2.1 checked0674.2.2.1 checked0674.2.2.2
    (power_identity10 plusWeights0674) (power_identity10 minusWeights0674) g hg hmax

def envelope0674 : Envelope := ⟨coefficients0674, upper0674, bound0674⟩

def coefficients0675 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-95/8192), (-5/2048), (-765/65536), (-725/131072)]

def upper0675 : ℚ := (62721/52428800000000)

def plusWeights0675 : Fin 11 → ℚ := ![(62721/52428800000000), (62721/5242880000000), (564489/10485760000000), (188163/1310720000000), (1317141/5242880000000), (3951423/13107200000000), (1317141/5242880000000), (186643/1310720000000), (527753/10485760000000), (220819/26214400000000), 0]

def minusWeights0675 : Fin 11 → ℚ := ![(62721/52428800000000), (62721/5242880000000), (564489/10485760000000), (188163/1310720000000), (1317141/5242880000000), (3951423/13107200000000), (1317141/5242880000000), (189683/1310720000000), (24049/419430400000), (406391/26214400000000), (62721/26214400000000)]

theorem checked0675 :
    (∀ i, 0 ≤ plusWeights0675 i) ∧
    (∀ i, 0 ≤ minusWeights0675 i) ∧
    (∀ i, plusCoefficients coefficients0675 upper0675 i = powerCoefficients10 plusWeights0675 i) ∧
    (∀ i, minusCoefficients coefficients0675 upper0675 i = powerCoefficients10 minusWeights0675 i) := by
  decide +kernel

theorem bound0675 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0675 g| ≤ (upper0675 : ℝ) :=
  abs_of_coefficients coefficients0675 upper0675 powerCoefficients10 plusWeights0675 minusWeights0675
    checked0675.1 checked0675.2.1 checked0675.2.2.1 checked0675.2.2.2
    (power_identity10 plusWeights0675) (power_identity10 minusWeights0675) g hg hmax

def envelope0675 : Envelope := ⟨coefficients0675, upper0675, bound0675⟩

def coefficients0676 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-85/8192), (-5/4096), (-165/8192), (-325/32768)]

def upper0676 : ℚ := (14037/13107200000000)

def plusWeights0676 : Fin 11 → ℚ := ![(14037/13107200000000), (14037/1310720000000), (126333/2621440000000), (42111/327680000000), (294777/1310720000000), (884331/3276800000000), (294777/1310720000000), (41771/327680000000), (118141/2621440000000), (49493/6553600000000), 0]

def minusWeights0676 : Fin 11 → ℚ := ![(14037/13107200000000), (14037/1310720000000), (126333/2621440000000), (42111/327680000000), (294777/1310720000000), (884331/3276800000000), (294777/1310720000000), (42451/327680000000), (5381/104857600000), (90877/6553600000000), (14037/6553600000000)]

theorem checked0676 :
    (∀ i, 0 ≤ plusWeights0676 i) ∧
    (∀ i, 0 ≤ minusWeights0676 i) ∧
    (∀ i, plusCoefficients coefficients0676 upper0676 i = powerCoefficients10 plusWeights0676 i) ∧
    (∀ i, minusCoefficients coefficients0676 upper0676 i = powerCoefficients10 minusWeights0676 i) := by
  decide +kernel

theorem bound0676 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0676 g| ≤ (upper0676 : ℝ) :=
  abs_of_coefficients coefficients0676 upper0676 powerCoefficients10 plusWeights0676 minusWeights0676
    checked0676.1 checked0676.2.1 checked0676.2.2.1 checked0676.2.2.2
    (power_identity10 plusWeights0676) (power_identity10 minusWeights0676) g hg hmax

def envelope0676 : Envelope := ⟨coefficients0676, upper0676, bound0676⟩

def coefficients0677 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-85/8192), (-5/4096), (-105/16384), (-25/8192)]

def upper0677 : ℚ := (1731/1638400000000)

def plusWeights0677 : Fin 11 → ℚ := ![(1731/1638400000000), (1731/163840000000), (15579/327680000000), (5193/40960000000), (36351/163840000000), (109053/409600000000), (36351/163840000000), (10301/81920000000), (2911/65536000000), (24319/3276800000000), 0]

def minusWeights0677 : Fin 11 → ℚ := ![(1731/1638400000000), (1731/163840000000), (15579/327680000000), (5193/40960000000), (36351/163840000000), (109053/409600000000), (36351/163840000000), (10471/81920000000), (16603/327680000000), (44921/3276800000000), (1731/819200000000)]

theorem checked0677 :
    (∀ i, 0 ≤ plusWeights0677 i) ∧
    (∀ i, 0 ≤ minusWeights0677 i) ∧
    (∀ i, plusCoefficients coefficients0677 upper0677 i = powerCoefficients10 plusWeights0677 i) ∧
    (∀ i, minusCoefficients coefficients0677 upper0677 i = powerCoefficients10 minusWeights0677 i) := by
  decide +kernel

theorem bound0677 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0677 g| ≤ (upper0677 : ℝ) :=
  abs_of_coefficients coefficients0677 upper0677 powerCoefficients10 plusWeights0677 minusWeights0677
    checked0677.1 checked0677.2.1 checked0677.2.2.1 checked0677.2.2.2
    (power_identity10 plusWeights0677) (power_identity10 minusWeights0677) g hg hmax

def envelope0677 : Envelope := ⟨coefficients0677, upper0677, bound0677⟩

def coefficients0678 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/512), (-5/512), (-315/16384), (-275/32768)]

def upper0678 : ℚ := (14343/13107200000000)

def plusWeights0678 : Fin 11 → ℚ := ![(14343/13107200000000), (14343/1310720000000), (129087/2621440000000), (43029/327680000000), (301203/1310720000000), (903609/3276800000000), (301203/1310720000000), (42709/327680000000), (121151/2621440000000), (51109/6553600000000), 0]

def minusWeights0678 : Fin 11 → ℚ := ![(14343/13107200000000), (14343/1310720000000), (129087/2621440000000), (43029/327680000000), (301203/1310720000000), (903609/3276800000000), (301203/1310720000000), (43349/327680000000), (137023/2621440000000), (92321/6553600000000), (14343/6553600000000)]

theorem checked0678 :
    (∀ i, 0 ≤ plusWeights0678 i) ∧
    (∀ i, 0 ≤ minusWeights0678 i) ∧
    (∀ i, plusCoefficients coefficients0678 upper0678 i = powerCoefficients10 plusWeights0678 i) ∧
    (∀ i, minusCoefficients coefficients0678 upper0678 i = powerCoefficients10 minusWeights0678 i) := by
  decide +kernel

theorem bound0678 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0678 g| ≤ (upper0678 : ℝ) :=
  abs_of_coefficients coefficients0678 upper0678 powerCoefficients10 plusWeights0678 minusWeights0678
    checked0678.1 checked0678.2.1 checked0678.2.2.1 checked0678.2.2.2
    (power_identity10 plusWeights0678) (power_identity10 minusWeights0678) g hg hmax

def envelope0678 : Envelope := ⟨coefficients0678, upper0678, bound0678⟩

def coefficients0679 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/512), (-5/512), (-15/1024), (-25/4096)]

def upper0679 : ℚ := (357/327680000000)

def plusWeights0679 : Fin 11 → ℚ := ![(357/327680000000), (357/32768000000), (3213/65536000000), (1071/8192000000), (7497/32768000000), (22491/81920000000), (7497/32768000000), (1063/8192000000), (15073/327680000000), (6353/819200000000), 0]

def minusWeights0679 : Fin 11 → ℚ := ![(357/327680000000), (357/32768000000), (3213/65536000000), (1071/8192000000), (7497/32768000000), (22491/81920000000), (7497/32768000000), (1079/8192000000), (17057/327680000000), (11497/819200000000), (357/163840000000)]

theorem checked0679 :
    (∀ i, 0 ≤ plusWeights0679 i) ∧
    (∀ i, 0 ≤ minusWeights0679 i) ∧
    (∀ i, plusCoefficients coefficients0679 upper0679 i = powerCoefficients10 plusWeights0679 i) ∧
    (∀ i, minusCoefficients coefficients0679 upper0679 i = powerCoefficients10 minusWeights0679 i) := by
  decide +kernel

theorem bound0679 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0679 g| ≤ (upper0679 : ℝ) :=
  abs_of_coefficients coefficients0679 upper0679 powerCoefficients10 plusWeights0679 minusWeights0679
    checked0679.1 checked0679.2.1 checked0679.2.2.1 checked0679.2.2.2
    (power_identity10 plusWeights0679) (power_identity10 minusWeights0679) g hg hmax

def envelope0679 : Envelope := ⟨coefficients0679, upper0679, bound0679⟩

def coefficients0680 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/512), (-5/512), (-165/16384), (-125/32768)]

def upper0680 : ℚ := (14217/13107200000000)

def plusWeights0680 : Fin 11 → ℚ := ![(14217/13107200000000), (14217/1310720000000), (127953/2621440000000), (42651/327680000000), (298557/1310720000000), (895671/3276800000000), (298557/1310720000000), (42331/327680000000), (120017/2621440000000), (50539/6553600000000), 0]

def minusWeights0680 : Fin 11 → ℚ := ![(14217/13107200000000), (14217/1310720000000), (127953/2621440000000), (42651/327680000000), (298557/1310720000000), (895671/3276800000000), (298557/1310720000000), (42971/327680000000), (135889/2621440000000), (91631/6553600000000), (14217/6553600000000)]

theorem checked0680 :
    (∀ i, 0 ≤ plusWeights0680 i) ∧
    (∀ i, 0 ≤ minusWeights0680 i) ∧
    (∀ i, plusCoefficients coefficients0680 upper0680 i = powerCoefficients10 plusWeights0680 i) ∧
    (∀ i, minusCoefficients coefficients0680 upper0680 i = powerCoefficients10 minusWeights0680 i) := by
  decide +kernel

theorem bound0680 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0680 g| ≤ (upper0680 : ℝ) :=
  abs_of_coefficients coefficients0680 upper0680 powerCoefficients10 plusWeights0680 minusWeights0680
    checked0680.1 checked0680.2.1 checked0680.2.2.1 checked0680.2.2.2
    (power_identity10 plusWeights0680) (power_identity10 minusWeights0680) g hg hmax

def envelope0680 : Envelope := ⟨coefficients0680, upper0680, bound0680⟩

def coefficients0681 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-39/4096), (-41/4096), (-269/32768), (-183/65536)]

def upper0681 : ℚ := (695163/655360000000000)

def plusWeights0681 : Fin 11 → ℚ := ![(695163/655360000000000), (695163/65536000000000), (6256467/131072000000000), (2085489/16384000000000), (14598423/65536000000000), (43795269/163840000000000), (14598423/65536000000000), (2069889/16384000000000), (5868947/131072000000000), (98861/13107200000000), 0]

def minusWeights0681 : Fin 11 → ℚ := ![(695163/655360000000000), (695163/65536000000000), (6256467/131072000000000), (2085489/16384000000000), (14598423/65536000000000), (43795269/163840000000000), (14598423/65536000000000), (2101089/16384000000000), (6643987/131072000000000), (896021/65536000000000), (695163/327680000000000)]

theorem checked0681 :
    (∀ i, 0 ≤ plusWeights0681 i) ∧
    (∀ i, 0 ≤ minusWeights0681 i) ∧
    (∀ i, plusCoefficients coefficients0681 upper0681 i = powerCoefficients10 plusWeights0681 i) ∧
    (∀ i, minusCoefficients coefficients0681 upper0681 i = powerCoefficients10 minusWeights0681 i) := by
  decide +kernel

theorem bound0681 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0681 g| ≤ (upper0681 : ℝ) :=
  abs_of_coefficients coefficients0681 upper0681 powerCoefficients10 plusWeights0681 minusWeights0681
    checked0681.1 checked0681.2.1 checked0681.2.2.1 checked0681.2.2.2
    (power_identity10 plusWeights0681) (power_identity10 minusWeights0681) g hg hmax

def envelope0681 : Envelope := ⟨coefficients0681, upper0681, bound0681⟩

def coefficients0682 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-19/2048), (-21/2048), (-19/1024), (-129/16384)]

def upper0682 : ℚ := (171969/163840000000000)

def plusWeights0682 : Fin 11 → ℚ := ![(171969/163840000000000), (171969/16384000000000), (1547721/32768000000000), (515907/4096000000000), (3611349/16384000000000), (10834047/40960000000000), (3611349/16384000000000), (512107/4096000000000), (1453161/32768000000000), (24541/3276800000000), 0]

def minusWeights0682 : Fin 11 → ℚ := ![(171969/163840000000000), (171969/16384000000000), (1547721/32768000000000), (515907/4096000000000), (3611349/16384000000000), (10834047/40960000000000), (3611349/16384000000000), (519707/4096000000000), (1642281/32768000000000), (221233/16384000000000), (171969/81920000000000)]

theorem checked0682 :
    (∀ i, 0 ≤ plusWeights0682 i) ∧
    (∀ i, 0 ≤ minusWeights0682 i) ∧
    (∀ i, plusCoefficients coefficients0682 upper0682 i = powerCoefficients10 plusWeights0682 i) ∧
    (∀ i, minusCoefficients coefficients0682 upper0682 i = powerCoefficients10 minusWeights0682 i) := by
  decide +kernel

theorem bound0682 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0682 g| ≤ (upper0682 : ℝ) :=
  abs_of_coefficients coefficients0682 upper0682 powerCoefficients10 plusWeights0682 minusWeights0682
    checked0682.1 checked0682.2.1 checked0682.2.2.1 checked0682.2.2.2
    (power_identity10 plusWeights0682) (power_identity10 minusWeights0682) g hg hmax

def envelope0682 : Envelope := ⟨coefficients0682, upper0682, bound0682⟩

def coefficients0683 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-19/2048), (-21/2048), (-129/16384), (-83/32768)]

def upper0683 : ℚ := (340263/327680000000000)

def plusWeights0683 : Fin 11 → ℚ := ![(340263/327680000000000), (340263/32768000000000), (3062367/65536000000000), (1020789/8192000000000), (7145523/32768000000000), (21436569/81920000000000), (7145523/32768000000000), (1013189/8192000000000), (2873247/65536000000000), (48417/6553600000000), 0]

def minusWeights0683 : Fin 11 → ℚ := ![(340263/327680000000000), (340263/32768000000000), (3062367/65536000000000), (1020789/8192000000000), (7145523/32768000000000), (21436569/81920000000000), (7145523/32768000000000), (1028389/8192000000000), (3251487/65536000000000), (438441/32768000000000), (340263/163840000000000)]

theorem checked0683 :
    (∀ i, 0 ≤ plusWeights0683 i) ∧
    (∀ i, 0 ≤ minusWeights0683 i) ∧
    (∀ i, plusCoefficients coefficients0683 upper0683 i = powerCoefficients10 plusWeights0683 i) ∧
    (∀ i, minusCoefficients coefficients0683 upper0683 i = powerCoefficients10 minusWeights0683 i) := by
  decide +kernel

theorem bound0683 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0683 g| ≤ (upper0683 : ℝ) :=
  abs_of_coefficients coefficients0683 upper0683 powerCoefficients10 plusWeights0683 minusWeights0683
    checked0683.1 checked0683.2.1 checked0683.2.2.1 checked0683.2.2.2
    (power_identity10 plusWeights0683) (power_identity10 minusWeights0683) g hg hmax

def envelope0683 : Envelope := ⟨coefficients0683, upper0683, bound0683⟩

def coefficients0684 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/8192), 0, (-375/65536), (-375/131072)]

def upper0684 : ℚ := (9663/10485760000000)

def plusWeights0684 : Fin 11 → ℚ := ![(9663/10485760000000), (9663/1048576000000), (86967/2097152000000), (28989/262144000000), (202923/1048576000000), (608769/2621440000000), (202923/1048576000000), (28749/262144000000), (81207/2097152000000), (6777/1048576000000), 0]

def minusWeights0684 : Fin 11 → ℚ := ![(9663/10485760000000), (9663/1048576000000), (86967/2097152000000), (28989/262144000000), (202923/1048576000000), (608769/2621440000000), (202923/1048576000000), (29229/262144000000), (92727/2097152000000), (12549/1048576000000), (9663/5242880000000)]

theorem checked0684 :
    (∀ i, 0 ≤ plusWeights0684 i) ∧
    (∀ i, 0 ≤ minusWeights0684 i) ∧
    (∀ i, plusCoefficients coefficients0684 upper0684 i = powerCoefficients10 plusWeights0684 i) ∧
    (∀ i, minusCoefficients coefficients0684 upper0684 i = powerCoefficients10 minusWeights0684 i) := by
  decide +kernel

theorem bound0684 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0684 g| ≤ (upper0684 : ℝ) :=
  abs_of_coefficients coefficients0684 upper0684 powerCoefficients10 plusWeights0684 minusWeights0684
    checked0684.1 checked0684.2.1 checked0684.2.2.1 checked0684.2.2.2
    (power_identity10 plusWeights0684) (power_identity10 minusWeights0684) g hg hmax

def envelope0684 : Envelope := ⟨coefficients0684, upper0684, bound0684⟩

def coefficients0685 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/8192), (225/32768), (225/65536), (1125/524288)]

def upper0685 : ℚ := (35367/41943040000000)

def plusWeights0685 : Fin 11 → ℚ := ![(35367/41943040000000), (35367/4194304000000), (318303/8388608000000), (106101/1048576000000), (742707/4194304000000), (2228121/10485760000000), (742707/4194304000000), (105141/1048576000000), (295839/8388608000000), (122187/20971520000000), 0]

def minusWeights0685 : Fin 11 → ℚ := ![(35367/41943040000000), (35367/4194304000000), (318303/8388608000000), (106101/1048576000000), (742707/4194304000000), (2228121/10485760000000), (742707/4194304000000), (107061/1048576000000), (340767/8388608000000), (231483/20971520000000), (35367/20971520000000)]

theorem checked0685 :
    (∀ i, 0 ≤ plusWeights0685 i) ∧
    (∀ i, 0 ≤ minusWeights0685 i) ∧
    (∀ i, plusCoefficients coefficients0685 upper0685 i = powerCoefficients10 plusWeights0685 i) ∧
    (∀ i, minusCoefficients coefficients0685 upper0685 i = powerCoefficients10 minusWeights0685 i) := by
  decide +kernel

theorem bound0685 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0685 g| ≤ (upper0685 : ℝ) :=
  abs_of_coefficients coefficients0685 upper0685 powerCoefficients10 plusWeights0685 minusWeights0685
    checked0685.1 checked0685.2.1 checked0685.2.2.1 checked0685.2.2.2
    (power_identity10 plusWeights0685) (power_identity10 minusWeights0685) g hg hmax

def envelope0685 : Envelope := ⟨coefficients0685, upper0685, bound0685⟩

def coefficients0686 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/8192), (325/32768), (325/65536), (1625/524288)]

def upper0686 : ℚ := (34019/41943040000000)

def plusWeights0686 : Fin 11 → ℚ := ![(34019/41943040000000), (34019/4194304000000), (306171/8388608000000), (102057/1048576000000), (714399/4194304000000), (2143197/10485760000000), (714399/4194304000000), (101097/1048576000000), (283963/8388608000000), (116759/20971520000000), 0]

def minusWeights0686 : Fin 11 → ℚ := ![(34019/41943040000000), (34019/4194304000000), (306171/8388608000000), (102057/1048576000000), (714399/4194304000000), (2143197/10485760000000), (714399/4194304000000), (103017/1048576000000), (328379/8388608000000), (223431/20971520000000), (34019/20971520000000)]

theorem checked0686 :
    (∀ i, 0 ≤ plusWeights0686 i) ∧
    (∀ i, 0 ≤ minusWeights0686 i) ∧
    (∀ i, plusCoefficients coefficients0686 upper0686 i = powerCoefficients10 plusWeights0686 i) ∧
    (∀ i, minusCoefficients coefficients0686 upper0686 i = powerCoefficients10 minusWeights0686 i) := by
  decide +kernel

theorem bound0686 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0686 g| ≤ (upper0686 : ℝ) :=
  abs_of_coefficients coefficients0686 upper0686 powerCoefficients10 plusWeights0686 minusWeights0686
    checked0686.1 checked0686.2.1 checked0686.2.2.1 checked0686.2.2.2
    (power_identity10 plusWeights0686) (power_identity10 minusWeights0686) g hg hmax

def envelope0686 : Envelope := ⟨coefficients0686, upper0686, bound0686⟩

def coefficients0687 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/8192), (375/32768), (375/65536), (1875/524288)]

def upper0687 : ℚ := (6669/8388608000000)

def plusWeights0687 : Fin 11 → ℚ := ![(6669/8388608000000), (6669/838860800000), (60021/1677721600000), (20007/209715200000), (140049/838860800000), (420147/2097152000000), (140049/838860800000), (3963/41943040000), (11121/335544320000), (22809/4194304000000), 0]

def minusWeights0687 : Fin 11 → ℚ := ![(6669/8388608000000), (6669/838860800000), (60021/1677721600000), (20007/209715200000), (140049/838860800000), (420147/2097152000000), (140049/838860800000), (20199/209715200000), (64437/1677721600000), (43881/4194304000000), (6669/4194304000000)]

theorem checked0687 :
    (∀ i, 0 ≤ plusWeights0687 i) ∧
    (∀ i, 0 ≤ minusWeights0687 i) ∧
    (∀ i, plusCoefficients coefficients0687 upper0687 i = powerCoefficients10 plusWeights0687 i) ∧
    (∀ i, minusCoefficients coefficients0687 upper0687 i = powerCoefficients10 minusWeights0687 i) := by
  decide +kernel

theorem bound0687 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0687 g| ≤ (upper0687 : ℝ) :=
  abs_of_coefficients coefficients0687 upper0687 powerCoefficients10 plusWeights0687 minusWeights0687
    checked0687.1 checked0687.2.1 checked0687.2.2.1 checked0687.2.2.2
    (power_identity10 plusWeights0687) (power_identity10 minusWeights0687) g hg hmax

def envelope0687 : Envelope := ⟨coefficients0687, upper0687, bound0687⟩

def coefficients0688 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-75/8192), (375/32768), (375/65536), (10125/524288)]

def upper0688 : ℚ := (33279/41943040000000)

def plusWeights0688 : Fin 11 → ℚ := ![(33279/41943040000000), (33279/4194304000000), (299511/8388608000000), (99837/1048576000000), (698859/4194304000000), (2096577/10485760000000), (698859/4194304000000), (98877/1048576000000), (277431/8388608000000), (22743/4194304000000), 0]

def minusWeights0688 : Fin 11 → ℚ := ![(33279/41943040000000), (33279/4194304000000), (299511/8388608000000), (99837/1048576000000), (698859/4194304000000), (2096577/10485760000000), (698859/4194304000000), (100797/1048576000000), (321591/8388608000000), (8763/838860800000), (33279/20971520000000)]

theorem checked0688 :
    (∀ i, 0 ≤ plusWeights0688 i) ∧
    (∀ i, 0 ≤ minusWeights0688 i) ∧
    (∀ i, plusCoefficients coefficients0688 upper0688 i = powerCoefficients10 plusWeights0688 i) ∧
    (∀ i, minusCoefficients coefficients0688 upper0688 i = powerCoefficients10 minusWeights0688 i) := by
  decide +kernel

theorem bound0688 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0688 g| ≤ (upper0688 : ℝ) :=
  abs_of_coefficients coefficients0688 upper0688 powerCoefficients10 plusWeights0688 minusWeights0688
    checked0688.1 checked0688.2.1 checked0688.2.2.1 checked0688.2.2.2
    (power_identity10 plusWeights0688) (power_identity10 minusWeights0688) g hg hmax

def envelope0688 : Envelope := ⟨coefficients0688, upper0688, bound0688⟩

def coefficients0689 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-37/4096), (-43/4096), (-447/32768), (-349/65536)]

def upper0689 : ℚ := (670089/655360000000000)

def plusWeights0689 : Fin 11 → ℚ := ![(670089/655360000000000), (670089/65536000000000), (6030801/131072000000000), (2010267/16384000000000), (14071869/65536000000000), (42215607/163840000000000), (14071869/65536000000000), (1995467/16384000000000), (5661841/131072000000000), (95567/13107200000000), 0]

def minusWeights0689 : Fin 11 → ℚ := ![(670089/655360000000000), (670089/65536000000000), (6030801/131072000000000), (2010267/16384000000000), (14071869/65536000000000), (42215607/163840000000000), (14071869/65536000000000), (2025067/16384000000000), (6399761/131072000000000), (862343/65536000000000), (670089/327680000000000)]

theorem checked0689 :
    (∀ i, 0 ≤ plusWeights0689 i) ∧
    (∀ i, 0 ≤ minusWeights0689 i) ∧
    (∀ i, plusCoefficients coefficients0689 upper0689 i = powerCoefficients10 plusWeights0689 i) ∧
    (∀ i, minusCoefficients coefficients0689 upper0689 i = powerCoefficients10 minusWeights0689 i) := by
  decide +kernel

theorem bound0689 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0689 g| ≤ (upper0689 : ℝ) :=
  abs_of_coefficients coefficients0689 upper0689 powerCoefficients10 plusWeights0689 minusWeights0689
    checked0689.1 checked0689.2.1 checked0689.2.2.1 checked0689.2.2.2
    (power_identity10 plusWeights0689) (power_identity10 minusWeights0689) g hg hmax

def envelope0689 : Envelope := ⟨coefficients0689, upper0689, bound0689⟩

def coefficients0690 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/1024), (-11/1024), (-393/16384), (-341/32768)]

def upper0690 : ℚ := (331401/327680000000000)

def plusWeights0690 : Fin 11 → ℚ := ![(331401/327680000000000), (331401/32768000000000), (2982609/65536000000000), (994203/8192000000000), (6959421/32768000000000), (20878263/81920000000000), (6959421/32768000000000), (987003/8192000000000), (2802769/65536000000000), (9487/1310720000000), 0]

def minusWeights0690 : Fin 11 → ℚ := ![(331401/327680000000000), (331401/32768000000000), (2982609/65536000000000), (994203/8192000000000), (6959421/32768000000000), (20878263/81920000000000), (6959421/32768000000000), (1001403/8192000000000), (3162449/65536000000000), (425627/32768000000000), (331401/163840000000000)]

theorem checked0690 :
    (∀ i, 0 ≤ plusWeights0690 i) ∧
    (∀ i, 0 ≤ minusWeights0690 i) ∧
    (∀ i, plusCoefficients coefficients0690 upper0690 i = powerCoefficients10 plusWeights0690 i) ∧
    (∀ i, minusCoefficients coefficients0690 upper0690 i = powerCoefficients10 minusWeights0690 i) := by
  decide +kernel

theorem bound0690 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0690 g| ≤ (upper0690 : ℝ) :=
  abs_of_coefficients coefficients0690 upper0690 powerCoefficients10 plusWeights0690 minusWeights0690
    checked0690.1 checked0690.2.1 checked0690.2.2.1 checked0690.2.2.2
    (power_identity10 plusWeights0690) (power_identity10 minusWeights0690) g hg hmax

def envelope0690 : Envelope := ⟨coefficients0690, upper0690, bound0690⟩

def coefficients0691 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/1024), (-11/1024), (-21/2048), (-29/8192)]

def upper0691 : ℚ := (81669/81920000000000)

def plusWeights0691 : Fin 11 → ℚ := ![(81669/81920000000000), (81669/8192000000000), (735021/16384000000000), (245007/2048000000000), (1715049/8192000000000), (5145147/20480000000000), (1715049/8192000000000), (243207/2048000000000), (690061/16384000000000), (2329/327680000000), 0]

def minusWeights0691 : Fin 11 → ℚ := ![(81669/81920000000000), (81669/8192000000000), (735021/16384000000000), (245007/2048000000000), (1715049/8192000000000), (5145147/20480000000000), (1715049/8192000000000), (246807/2048000000000), (779981/16384000000000), (105113/8192000000000), (81669/40960000000000)]

theorem checked0691 :
    (∀ i, 0 ≤ plusWeights0691 i) ∧
    (∀ i, 0 ≤ minusWeights0691 i) ∧
    (∀ i, plusCoefficients coefficients0691 upper0691 i = powerCoefficients10 plusWeights0691 i) ∧
    (∀ i, minusCoefficients coefficients0691 upper0691 i = powerCoefficients10 minusWeights0691 i) := by
  decide +kernel

theorem bound0691 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0691 g| ≤ (upper0691 : ℝ) :=
  abs_of_coefficients coefficients0691 upper0691 powerCoefficients10 plusWeights0691 minusWeights0691
    checked0691.1 checked0691.2.1 checked0691.2.2.1 checked0691.2.2.2
    (power_identity10 plusWeights0691) (power_identity10 minusWeights0691) g hg hmax

def envelope0691 : Envelope := ⟨coefficients0691, upper0691, bound0691⟩

def coefficients0692 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/2048), (-15/2048), (-685/32768), (-625/65536)]

def upper0692 : ℚ := (21693/26214400000000)

def plusWeights0692 : Fin 11 → ℚ := ![(21693/26214400000000), (21693/2621440000000), (195237/5242880000000), (65079/655360000000), (455553/2621440000000), (1366659/6553600000000), (455553/2621440000000), (64599/655360000000), (183333/5242880000000), (77471/13107200000000), 0]

def minusWeights0692 : Fin 11 → ℚ := ![(21693/26214400000000), (21693/2621440000000), (195237/5242880000000), (65079/655360000000), (455553/2621440000000), (1366659/6553600000000), (455553/2621440000000), (65559/655360000000), (207141/5242880000000), (139459/13107200000000), (21693/13107200000000)]

theorem checked0692 :
    (∀ i, 0 ≤ plusWeights0692 i) ∧
    (∀ i, 0 ≤ minusWeights0692 i) ∧
    (∀ i, plusCoefficients coefficients0692 upper0692 i = powerCoefficients10 plusWeights0692 i) ∧
    (∀ i, minusCoefficients coefficients0692 upper0692 i = powerCoefficients10 minusWeights0692 i) := by
  decide +kernel

theorem bound0692 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0692 g| ≤ (upper0692 : ℝ) :=
  abs_of_coefficients coefficients0692 upper0692 powerCoefficients10 plusWeights0692 minusWeights0692
    checked0692.1 checked0692.2.1 checked0692.2.2.1 checked0692.2.2.2
    (power_identity10 plusWeights0692) (power_identity10 minusWeights0692) g hg hmax

def envelope0692 : Envelope := ⟨coefficients0692, upper0692, bound0692⟩

def coefficients0693 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/2048), (-15/2048), (-135/32768), (-75/65536)]

def upper0693 : ℚ := (21231/26214400000000)

def plusWeights0693 : Fin 11 → ℚ := ![(21231/26214400000000), (21231/2621440000000), (191079/5242880000000), (63693/655360000000), (445851/2621440000000), (1337553/6553600000000), (445851/2621440000000), (63213/655360000000), (7167/209715200000), (75381/13107200000000), 0]

def minusWeights0693 : Fin 11 → ℚ := ![(21231/26214400000000), (21231/2621440000000), (191079/5242880000000), (63693/655360000000), (445851/2621440000000), (1337553/6553600000000), (445851/2621440000000), (64173/655360000000), (202983/5242880000000), (136929/13107200000000), (21231/13107200000000)]

theorem checked0693 :
    (∀ i, 0 ≤ plusWeights0693 i) ∧
    (∀ i, 0 ≤ minusWeights0693 i) ∧
    (∀ i, plusCoefficients coefficients0693 upper0693 i = powerCoefficients10 plusWeights0693 i) ∧
    (∀ i, minusCoefficients coefficients0693 upper0693 i = powerCoefficients10 minusWeights0693 i) := by
  decide +kernel

theorem bound0693 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0693 g| ≤ (upper0693 : ℝ) :=
  abs_of_coefficients coefficients0693 upper0693 powerCoefficients10 plusWeights0693 minusWeights0693
    checked0693.1 checked0693.2.1 checked0693.2.2.1 checked0693.2.2.2
    (power_identity10 plusWeights0693) (power_identity10 minusWeights0693) g hg hmax

def envelope0693 : Envelope := ⟨coefficients0693, upper0693, bound0693⟩

def coefficients0694 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/2048), (405/32768), (825/65536), (3075/524288)]

def upper0694 : ℚ := (124917/209715200000000)

def plusWeights0694 : Fin 11 → ℚ := ![(124917/209715200000000), (124917/20971520000000), (1124253/41943040000000), (374751/5242880000000), (2623257/20971520000000), (7869771/52428800000000), (2623257/20971520000000), (370911/5242880000000), (1037277/41943040000000), (16857/4194304000000), 0]

def minusWeights0694 : Fin 11 → ℚ := ![(124917/209715200000000), (124917/20971520000000), (1124253/41943040000000), (374751/5242880000000), (2623257/20971520000000), (7869771/52428800000000), (2623257/20971520000000), (378591/5242880000000), (1211229/41943040000000), (165549/20971520000000), (124917/104857600000000)]

theorem checked0694 :
    (∀ i, 0 ≤ plusWeights0694 i) ∧
    (∀ i, 0 ≤ minusWeights0694 i) ∧
    (∀ i, plusCoefficients coefficients0694 upper0694 i = powerCoefficients10 plusWeights0694 i) ∧
    (∀ i, minusCoefficients coefficients0694 upper0694 i = powerCoefficients10 minusWeights0694 i) := by
  decide +kernel

theorem bound0694 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0694 g| ≤ (upper0694 : ℝ) :=
  abs_of_coefficients coefficients0694 upper0694 powerCoefficients10 plusWeights0694 minusWeights0694
    checked0694.1 checked0694.2.1 checked0694.2.2.1 checked0694.2.2.2
    (power_identity10 plusWeights0694) (power_identity10 minusWeights0694) g hg hmax

def envelope0694 : Envelope := ⟨coefficients0694, upper0694, bound0694⟩

def coefficients0695 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/4096), (-33/4096), (-627/32768), (-549/65536)]

def upper0695 : ℚ := (497889/655360000000000)

def plusWeights0695 : Fin 11 → ℚ := ![(497889/655360000000000), (497889/65536000000000), (4481001/131072000000000), (1493667/16384000000000), (10455669/65536000000000), (31367007/163840000000000), (10455669/65536000000000), (1482867/16384000000000), (4211241/131072000000000), (14259/2621440000000), 0]

def minusWeights0695 : Fin 11 → ℚ := ![(497889/655360000000000), (497889/65536000000000), (4481001/131072000000000), (1493667/16384000000000), (10455669/65536000000000), (31367007/163840000000000), (10455669/65536000000000), (1504467/16384000000000), (4750761/131072000000000), (639303/65536000000000), (497889/327680000000000)]

theorem checked0695 :
    (∀ i, 0 ≤ plusWeights0695 i) ∧
    (∀ i, 0 ≤ minusWeights0695 i) ∧
    (∀ i, plusCoefficients coefficients0695 upper0695 i = powerCoefficients10 plusWeights0695 i) ∧
    (∀ i, minusCoefficients coefficients0695 upper0695 i = powerCoefficients10 minusWeights0695 i) := by
  decide +kernel

theorem bound0695 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0695 g| ≤ (upper0695 : ℝ) :=
  abs_of_coefficients coefficients0695 upper0695 powerCoefficients10 plusWeights0695 minusWeights0695
    checked0695.1 checked0695.2.1 checked0695.2.2.1 checked0695.2.2.2
    (power_identity10 plusWeights0695) (power_identity10 minusWeights0695) g hg hmax

def envelope0695 : Envelope := ⟨coefficients0695, upper0695, bound0695⟩

def coefficients0696 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/4096), (-33/4096), (-477/32768), (-399/65536)]

def upper0696 : ℚ := (494739/655360000000000)

def plusWeights0696 : Fin 11 → ℚ := ![(494739/655360000000000), (494739/65536000000000), (4452651/131072000000000), (1484217/16384000000000), (10389519/65536000000000), (31168557/163840000000000), (10389519/65536000000000), (1473417/16384000000000), (4182891/131072000000000), (2829/524288000000), 0]

def minusWeights0696 : Fin 11 → ℚ := ![(494739/655360000000000), (494739/65536000000000), (4452651/131072000000000), (1484217/16384000000000), (10389519/65536000000000), (31168557/163840000000000), (10389519/65536000000000), (1495017/16384000000000), (4722411/131072000000000), (635853/65536000000000), (494739/327680000000000)]

theorem checked0696 :
    (∀ i, 0 ≤ plusWeights0696 i) ∧
    (∀ i, 0 ≤ minusWeights0696 i) ∧
    (∀ i, plusCoefficients coefficients0696 upper0696 i = powerCoefficients10 plusWeights0696 i) ∧
    (∀ i, minusCoefficients coefficients0696 upper0696 i = powerCoefficients10 minusWeights0696 i) := by
  decide +kernel

theorem bound0696 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0696 g| ≤ (upper0696 : ℝ) :=
  abs_of_coefficients coefficients0696 upper0696 powerCoefficients10 plusWeights0696 minusWeights0696
    checked0696.1 checked0696.2.1 checked0696.2.2.1 checked0696.2.2.2
    (power_identity10 plusWeights0696) (power_identity10 minusWeights0696) g hg hmax

def envelope0696 : Envelope := ⟨coefficients0696, upper0696, bound0696⟩

def coefficients0697 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/4096), (-33/4096), (-201/16384), (-81/16384)]

def upper0697 : ℚ := (123291/163840000000000)

def plusWeights0697 : Fin 11 → ℚ := ![(123291/163840000000000), (123291/16384000000000), (1109619/32768000000000), (369873/4096000000000), (2589111/16384000000000), (7767333/40960000000000), (2589111/16384000000000), (367173/4096000000000), (1042179/32768000000000), (1761/327680000000), 0]

def minusWeights0697 : Fin 11 → ℚ := ![(123291/163840000000000), (123291/16384000000000), (1109619/32768000000000), (369873/4096000000000), (2589111/16384000000000), (7767333/40960000000000), (2589111/16384000000000), (372573/4096000000000), (1177059/32768000000000), (39633/4096000000000), (123291/81920000000000)]

theorem checked0697 :
    (∀ i, 0 ≤ plusWeights0697 i) ∧
    (∀ i, 0 ≤ minusWeights0697 i) ∧
    (∀ i, plusCoefficients coefficients0697 upper0697 i = powerCoefficients10 plusWeights0697 i) ∧
    (∀ i, minusCoefficients coefficients0697 upper0697 i = powerCoefficients10 minusWeights0697 i) := by
  decide +kernel

theorem bound0697 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0697 g| ≤ (upper0697 : ℝ) :=
  abs_of_coefficients coefficients0697 upper0697 powerCoefficients10 plusWeights0697 minusWeights0697
    checked0697.1 checked0697.2.1 checked0697.2.2.1 checked0697.2.2.2
    (power_identity10 plusWeights0697) (power_identity10 minusWeights0697) g hg hmax

def envelope0697 : Envelope := ⟨coefficients0697, upper0697, bound0697⟩

def coefficients0698 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-25/4096), (175/16384), (175/32768), (875/262144)]

def upper0698 : ℚ := (10441/20971520000000)

def plusWeights0698 : Fin 11 → ℚ := ![(10441/20971520000000), (10441/2097152000000), (93969/4194304000000), (31323/524288000000), (219261/2097152000000), (657783/5242880000000), (219261/2097152000000), (31003/524288000000), (86737/4194304000000), (35301/10485760000000), 0]

def minusWeights0698 : Fin 11 → ℚ := ![(10441/20971520000000), (10441/2097152000000), (93969/4194304000000), (31323/524288000000), (219261/2097152000000), (657783/5242880000000), (219261/2097152000000), (31643/524288000000), (101201/4194304000000), (69109/10485760000000), (10441/10485760000000)]

theorem checked0698 :
    (∀ i, 0 ≤ plusWeights0698 i) ∧
    (∀ i, 0 ≤ minusWeights0698 i) ∧
    (∀ i, plusCoefficients coefficients0698 upper0698 i = powerCoefficients10 plusWeights0698 i) ∧
    (∀ i, minusCoefficients coefficients0698 upper0698 i = powerCoefficients10 minusWeights0698 i) := by
  decide +kernel

theorem bound0698 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0698 g| ≤ (upper0698 : ℝ) :=
  abs_of_coefficients coefficients0698 upper0698 powerCoefficients10 plusWeights0698 minusWeights0698
    checked0698.1 checked0698.2.1 checked0698.2.2.1 checked0698.2.2.2
    (power_identity10 plusWeights0698) (power_identity10 minusWeights0698) g hg hmax

def envelope0698 : Envelope := ⟨coefficients0698, upper0698, bound0698⟩

def coefficients0699 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/1024), (-5/1024), (-415/32768), (-375/65536)]

def upper0699 : ℚ := (14427/26214400000000)

def plusWeights0699 : Fin 11 → ℚ := ![(14427/26214400000000), (14427/2621440000000), (129843/5242880000000), (43281/655360000000), (302967/2621440000000), (908901/6553600000000), (302967/2621440000000), (42961/655360000000), (121907/5242880000000), (51489/13107200000000), 0]

def minusWeights0699 : Fin 11 → ℚ := ![(14427/26214400000000), (14427/2621440000000), (129843/5242880000000), (43281/655360000000), (302967/2621440000000), (908901/6553600000000), (302967/2621440000000), (43601/655360000000), (137779/5242880000000), (92781/13107200000000), (14427/13107200000000)]

theorem checked0699 :
    (∀ i, 0 ≤ plusWeights0699 i) ∧
    (∀ i, 0 ≤ minusWeights0699 i) ∧
    (∀ i, plusCoefficients coefficients0699 upper0699 i = powerCoefficients10 plusWeights0699 i) ∧
    (∀ i, minusCoefficients coefficients0699 upper0699 i = powerCoefficients10 minusWeights0699 i) := by
  decide +kernel

theorem bound0699 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0699 g| ≤ (upper0699 : ℝ) :=
  abs_of_coefficients coefficients0699 upper0699 powerCoefficients10 plusWeights0699 minusWeights0699
    checked0699.1 checked0699.2.1 checked0699.2.2.1 checked0699.2.2.2
    (power_identity10 plusWeights0699) (power_identity10 minusWeights0699) g hg hmax

def envelope0699 : Envelope := ⟨coefficients0699, upper0699, bound0699⟩

def coefficients0700 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/1024), (-5/1024), (-85/8192), (-75/16384)]

def upper0700 : ℚ := (3591/6553600000000)

def plusWeights0700 : Fin 11 → ℚ := ![(3591/6553600000000), (3591/655360000000), (32319/1310720000000), (10773/163840000000), (75411/655360000000), (226233/1638400000000), (75411/655360000000), (10693/163840000000), (6067/262144000000), (12801/3276800000000), 0]

def minusWeights0700 : Fin 11 → ℚ := ![(3591/6553600000000), (3591/655360000000), (32319/1310720000000), (10773/163840000000), (75411/655360000000), (226233/1638400000000), (75411/655360000000), (10853/163840000000), (34303/1310720000000), (23109/3276800000000), (3591/3276800000000)]

theorem checked0700 :
    (∀ i, 0 ≤ plusWeights0700 i) ∧
    (∀ i, 0 ≤ minusWeights0700 i) ∧
    (∀ i, plusCoefficients coefficients0700 upper0700 i = powerCoefficients10 plusWeights0700 i) ∧
    (∀ i, minusCoefficients coefficients0700 upper0700 i = powerCoefficients10 minusWeights0700 i) := by
  decide +kernel

theorem bound0700 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0700 g| ≤ (upper0700 : ℝ) :=
  abs_of_coefficients coefficients0700 upper0700 powerCoefficients10 plusWeights0700 minusWeights0700
    checked0700.1 checked0700.2.1 checked0700.2.2.1 checked0700.2.2.2
    (power_identity10 plusWeights0700) (power_identity10 minusWeights0700) g hg hmax

def envelope0700 : Envelope := ⟨coefficients0700, upper0700, bound0700⟩

def coefficients0701 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/1024), (-5/1024), (-15/2048), (-25/8192)]

def upper0701 : ℚ := (357/655360000000)

def plusWeights0701 : Fin 11 → ℚ := ![(357/655360000000), (357/65536000000), (3213/131072000000), (1071/16384000000), (7497/65536000000), (22491/163840000000), (7497/65536000000), (1063/16384000000), (15073/655360000000), (6353/1638400000000), 0]

def minusWeights0701 : Fin 11 → ℚ := ![(357/655360000000), (357/65536000000), (3213/131072000000), (1071/16384000000), (7497/65536000000), (22491/163840000000), (7497/65536000000), (1079/16384000000), (17057/655360000000), (11497/1638400000000), (357/327680000000)]

theorem checked0701 :
    (∀ i, 0 ≤ plusWeights0701 i) ∧
    (∀ i, 0 ≤ minusWeights0701 i) ∧
    (∀ i, plusCoefficients coefficients0701 upper0701 i = powerCoefficients10 plusWeights0701 i) ∧
    (∀ i, minusCoefficients coefficients0701 upper0701 i = powerCoefficients10 minusWeights0701 i) := by
  decide +kernel

theorem bound0701 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0701 g| ≤ (upper0701 : ℝ) :=
  abs_of_coefficients coefficients0701 upper0701 powerCoefficients10 plusWeights0701 minusWeights0701
    checked0701.1 checked0701.2.1 checked0701.2.2.1 checked0701.2.2.2
    (power_identity10 plusWeights0701) (power_identity10 minusWeights0701) g hg hmax

def envelope0701 : Envelope := ⟨coefficients0701, upper0701, bound0701⟩

def coefficients0702 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/2048), (-11/2048), (-593/32768), (-541/65536)]

def upper0702 : ℚ := (335601/655360000000000)

def plusWeights0702 : Fin 11 → ℚ := ![(335601/655360000000000), (335601/65536000000000), (3020409/131072000000000), (1006803/16384000000000), (7047621/65536000000000), (21142863/163840000000000), (7047621/65536000000000), (999603/16384000000000), (2840569/131072000000000), (9639/2621440000000), 0]

def minusWeights0702 : Fin 11 → ℚ := ![(335601/655360000000000), (335601/65536000000000), (3020409/131072000000000), (1006803/16384000000000), (7047621/65536000000000), (21142863/163840000000000), (7047621/65536000000000), (1014003/16384000000000), (3200249/131072000000000), (430227/65536000000000), (335601/327680000000000)]

theorem checked0702 :
    (∀ i, 0 ≤ plusWeights0702 i) ∧
    (∀ i, 0 ≤ minusWeights0702 i) ∧
    (∀ i, plusCoefficients coefficients0702 upper0702 i = powerCoefficients10 plusWeights0702 i) ∧
    (∀ i, minusCoefficients coefficients0702 upper0702 i = powerCoefficients10 minusWeights0702 i) := by
  decide +kernel

theorem bound0702 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0702 g| ≤ (upper0702 : ℝ) :=
  abs_of_coefficients coefficients0702 upper0702 powerCoefficients10 plusWeights0702 minusWeights0702
    checked0702.1 checked0702.2.1 checked0702.2.2.1 checked0702.2.2.2
    (power_identity10 plusWeights0702) (power_identity10 minusWeights0702) g hg hmax

def envelope0702 : Envelope := ⟨coefficients0702, upper0702, bound0702⟩

def coefficients0703 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/2048), (-11/2048), (-71/4096), (-129/16384)]

def upper0703 : ℚ := (83769/163840000000000)

def plusWeights0703 : Fin 11 → ℚ := ![(83769/163840000000000), (83769/16384000000000), (753921/32768000000000), (251307/4096000000000), (1759149/16384000000000), (5277447/40960000000000), (1759149/16384000000000), (249507/4096000000000), (708961/32768000000000), (481/131072000000), 0]

def minusWeights0703 : Fin 11 → ℚ := ![(83769/163840000000000), (83769/16384000000000), (753921/32768000000000), (251307/4096000000000), (1759149/16384000000000), (5277447/40960000000000), (1759149/16384000000000), (253107/4096000000000), (798881/32768000000000), (107413/16384000000000), (83769/81920000000000)]

theorem checked0703 :
    (∀ i, 0 ≤ plusWeights0703 i) ∧
    (∀ i, 0 ≤ minusWeights0703 i) ∧
    (∀ i, plusCoefficients coefficients0703 upper0703 i = powerCoefficients10 plusWeights0703 i) ∧
    (∀ i, minusCoefficients coefficients0703 upper0703 i = powerCoefficients10 minusWeights0703 i) := by
  decide +kernel

theorem bound0703 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0703 g| ≤ (upper0703 : ℝ) :=
  abs_of_coefficients coefficients0703 upper0703 powerCoefficients10 plusWeights0703 minusWeights0703
    checked0703.1 checked0703.2.1 checked0703.2.2.1 checked0703.2.2.2
    (power_identity10 plusWeights0703) (power_identity10 minusWeights0703) g hg hmax

def envelope0703 : Envelope := ⟨coefficients0703, upper0703, bound0703⟩

end BilayerDressed.CubicQuarticEnvelopes

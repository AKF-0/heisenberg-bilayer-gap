import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0160 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/512), (-125/4096), (-15/2048), (-615/8192), (-75/2048)]

def upper0160 : ℚ := (21249/1638400000000)

def plusWeights0160 : Fin 11 → ℚ := ![(21249/1638400000000), (21249/163840000000), (191241/327680000000), (63747/40960000000), (446229/163840000000), (1338687/409600000000), (444629/163840000000), (31011/20480000000), (169017/327680000000), (133127/1638400000000), 0]

def minusWeights0160 : Fin 11 → ℚ := ![(21249/1638400000000), (21249/163840000000), (191241/327680000000), (63747/40960000000), (446229/163840000000), (1338687/409600000000), (447829/163840000000), (1023/640000000), (42693/65536000000), (291853/1638400000000), (21249/819200000000)]

theorem checked0160 :
    (∀ i, 0 ≤ plusWeights0160 i) ∧
    (∀ i, 0 ≤ minusWeights0160 i) ∧
    (∀ i, plusCoefficients coefficients0160 upper0160 i = powerCoefficients10 plusWeights0160 i) ∧
    (∀ i, minusCoefficients coefficients0160 upper0160 i = powerCoefficients10 minusWeights0160 i) := by
  decide +kernel

theorem bound0160 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0160 g| ≤ (upper0160 : ℝ) :=
  abs_of_coefficients coefficients0160 upper0160 powerCoefficients10 plusWeights0160 minusWeights0160
    checked0160.1 checked0160.2.1 checked0160.2.2.1 checked0160.2.2.2
    (power_identity10 plusWeights0160) (power_identity10 minusWeights0160) g hg hmax

def envelope0160 : Envelope := ⟨coefficients0160, upper0160, bound0160⟩

def coefficients0161 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/512), (-125/4096), (-15/2048), (-165/8192), (-75/8192)]

def upper0161 : ℚ := (42309/3276800000000)

def plusWeights0161 : Fin 11 → ℚ := ![(42309/3276800000000), (42309/327680000000), (380781/655360000000), (126927/81920000000), (888489/327680000000), (2665467/819200000000), (885289/327680000000), (123477/81920000000), (336333/655360000000), (8267/102400000000), 0]

def minusWeights0161 : Fin 11 → ℚ := ![(42309/3276800000000), (42309/327680000000), (380781/655360000000), (126927/81920000000), (888489/327680000000), (2665467/819200000000), (891689/327680000000), (130377/81920000000), (425229/655360000000), (145409/819200000000), (42309/1638400000000)]

theorem checked0161 :
    (∀ i, 0 ≤ plusWeights0161 i) ∧
    (∀ i, 0 ≤ minusWeights0161 i) ∧
    (∀ i, plusCoefficients coefficients0161 upper0161 i = powerCoefficients10 plusWeights0161 i) ∧
    (∀ i, minusCoefficients coefficients0161 upper0161 i = powerCoefficients10 minusWeights0161 i) := by
  decide +kernel

theorem bound0161 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0161 g| ≤ (upper0161 : ℝ) :=
  abs_of_coefficients coefficients0161 upper0161 powerCoefficients10 plusWeights0161 minusWeights0161
    checked0161.1 checked0161.2.1 checked0161.2.2.1 checked0161.2.2.2
    (power_identity10 plusWeights0161) (power_identity10 minusWeights0161) g hg hmax

def envelope0161 : Envelope := ⟨coefficients0161, upper0161, bound0161⟩

def coefficients0162 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/512), (-125/4096), (-15/2048), (-255/16384), (-225/32768)]

def upper0162 : ℚ := (169173/13107200000000)

def plusWeights0162 : Fin 11 → ℚ := ![(169173/13107200000000), (169173/1310720000000), (1522557/2621440000000), (507519/327680000000), (3552633/1310720000000), (10657899/3276800000000), (3539833/1310720000000), (493719/327680000000), (268953/524288000000), (528803/6553600000000), 0]

def minusWeights0162 : Fin 11 → ℚ := ![(169173/13107200000000), (169173/1310720000000), (1522557/2621440000000), (507519/327680000000), (3552633/1310720000000), (10657899/3276800000000), (3565433/1310720000000), (521319/327680000000), (1700349/2621440000000), (1162927/6553600000000), (169173/6553600000000)]

theorem checked0162 :
    (∀ i, 0 ≤ plusWeights0162 i) ∧
    (∀ i, 0 ≤ minusWeights0162 i) ∧
    (∀ i, plusCoefficients coefficients0162 upper0162 i = powerCoefficients10 plusWeights0162 i) ∧
    (∀ i, minusCoefficients coefficients0162 upper0162 i = powerCoefficients10 minusWeights0162 i) := by
  decide +kernel

theorem bound0162 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0162 g| ≤ (upper0162 : ℝ) :=
  abs_of_coefficients coefficients0162 upper0162 powerCoefficients10 plusWeights0162 minusWeights0162
    checked0162.1 checked0162.2.1 checked0162.2.2.1 checked0162.2.2.2
    (power_identity10 plusWeights0162) (power_identity10 minusWeights0162) g hg hmax

def envelope0162 : Envelope := ⟨coefficients0162, upper0162, bound0162⟩

def coefficients0163 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/512), (-145/8192), (-15/4096), (-555/32768), (-525/65536)]

def upper0163 : ℚ := (12153/1048576000000)

def plusWeights0163 : Fin 11 → ℚ := ![(12153/1048576000000), (12153/104857600000), (109377/209715200000), (36459/26214400000), (255213/104857600000), (765639/262144000000), (254189/104857600000), (176943/131072000000), (2399193/5242880000000), (936343/13107200000000), 0]

def minusWeights0163 : Fin 11 → ℚ := ![(12153/1048576000000), (12153/104857600000), (109377/209715200000), (36459/26214400000), (255213/104857600000), (765639/262144000000), (256237/104857600000), (187647/131072000000), (3069657/5242880000000), (2101907/13107200000000), (12153/524288000000)]

theorem checked0163 :
    (∀ i, 0 ≤ plusWeights0163 i) ∧
    (∀ i, 0 ≤ minusWeights0163 i) ∧
    (∀ i, plusCoefficients coefficients0163 upper0163 i = powerCoefficients10 plusWeights0163 i) ∧
    (∀ i, minusCoefficients coefficients0163 upper0163 i = powerCoefficients10 minusWeights0163 i) := by
  decide +kernel

theorem bound0163 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0163 g| ≤ (upper0163 : ℝ) :=
  abs_of_coefficients coefficients0163 upper0163 powerCoefficients10 plusWeights0163 minusWeights0163
    checked0163.1 checked0163.2.1 checked0163.2.2.1 checked0163.2.2.2
    (power_identity10 plusWeights0163) (power_identity10 minusWeights0163) g hg hmax

def envelope0163 : Envelope := ⟨coefficients0163, upper0163, bound0163⟩

def coefficients0164 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/1024), (-245/8192), (-75/4096), (-375/8192), (-675/32768)]

def upper0164 : ℚ := (106227/13107200000000)

def plusWeights0164 : Fin 11 → ℚ := ![(106227/13107200000000), (106227/1310720000000), (956043/2621440000000), (318681/327680000000), (2230767/1310720000000), (6692301/3276800000000), (2224367/1310720000000), (311301/327680000000), (855243/2621440000000), (68327/1310720000000), 0]

def minusWeights0164 : Fin 11 → ℚ := ![(106227/13107200000000), (106227/1310720000000), (956043/2621440000000), (318681/327680000000), (2230767/1310720000000), (6692301/3276800000000), (2237167/1310720000000), (326061/327680000000), (1056843/2621440000000), (144127/1310720000000), (106227/6553600000000)]

theorem checked0164 :
    (∀ i, 0 ≤ plusWeights0164 i) ∧
    (∀ i, 0 ≤ minusWeights0164 i) ∧
    (∀ i, plusCoefficients coefficients0164 upper0164 i = powerCoefficients10 plusWeights0164 i) ∧
    (∀ i, minusCoefficients coefficients0164 upper0164 i = powerCoefficients10 minusWeights0164 i) := by
  decide +kernel

theorem bound0164 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0164 g| ≤ (upper0164 : ℝ) :=
  abs_of_coefficients coefficients0164 upper0164 powerCoefficients10 plusWeights0164 minusWeights0164
    checked0164.1 checked0164.2.1 checked0164.2.2.1 checked0164.2.2.2
    (power_identity10 plusWeights0164) (power_identity10 minusWeights0164) g hg hmax

def envelope0164 : Envelope := ⟨coefficients0164, upper0164, bound0164⟩

def coefficients0165 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/1024), (-125/8192), (-15/4096), (-15/1024), (-225/32768)]

def upper0165 : ℚ := (84681/13107200000000)

def plusWeights0165 : Fin 11 → ℚ := ![(84681/13107200000000), (84681/1310720000000), (762129/2621440000000), (254043/327680000000), (1778301/1310720000000), (5334903/3276800000000), (1771901/1310720000000), (247143/327680000000), (673233/2621440000000), (264829/6553600000000), 0]

def minusWeights0165 : Fin 11 → ℚ := ![(84681/13107200000000), (84681/1310720000000), (762129/2621440000000), (254043/327680000000), (1778301/1310720000000), (5334903/3276800000000), (1784701/1310720000000), (260943/327680000000), (34041/104857600000), (581981/6553600000000), (84681/6553600000000)]

theorem checked0165 :
    (∀ i, 0 ≤ plusWeights0165 i) ∧
    (∀ i, 0 ≤ minusWeights0165 i) ∧
    (∀ i, plusCoefficients coefficients0165 upper0165 i = powerCoefficients10 plusWeights0165 i) ∧
    (∀ i, minusCoefficients coefficients0165 upper0165 i = powerCoefficients10 minusWeights0165 i) := by
  decide +kernel

theorem bound0165 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0165 g| ≤ (upper0165 : ℝ) :=
  abs_of_coefficients coefficients0165 upper0165 powerCoefficients10 plusWeights0165 minusWeights0165
    checked0165.1 checked0165.2.1 checked0165.2.2.1 checked0165.2.2.2
    (power_identity10 plusWeights0165) (power_identity10 minusWeights0165) g hg hmax

def envelope0165 : Envelope := ⟨coefficients0165, upper0165, bound0165⟩

def coefficients0166 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/1024), (-25/2048), (265/32768), (725/65536), (2825/524288)]

def upper0166 : ℚ := (1260607/209715200000000)

def plusWeights0166 : Fin 11 → ℚ := ![(1260607/209715200000000), (1260607/20971520000000), (11345463/41943040000000), (3781821/5242880000000), (26472747/20971520000000), (79418241/52428800000000), (26370347/20971520000000), (3673021/5242880000000), (1993291/8388608000000), (777831/20971520000000), 0]

def minusWeights0166 : Fin 11 → ℚ := ![(1260607/209715200000000), (1260607/20971520000000), (11345463/41943040000000), (3781821/5242880000000), (26472747/20971520000000), (79418241/52428800000000), (26575147/20971520000000), (3890621/5242880000000), (12724471/41943040000000), (1743383/20971520000000), (1260607/104857600000000)]

theorem checked0166 :
    (∀ i, 0 ≤ plusWeights0166 i) ∧
    (∀ i, 0 ≤ minusWeights0166 i) ∧
    (∀ i, plusCoefficients coefficients0166 upper0166 i = powerCoefficients10 plusWeights0166 i) ∧
    (∀ i, minusCoefficients coefficients0166 upper0166 i = powerCoefficients10 minusWeights0166 i) := by
  decide +kernel

theorem bound0166 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0166 g| ≤ (upper0166 : ℝ) :=
  abs_of_coefficients coefficients0166 upper0166 powerCoefficients10 plusWeights0166 minusWeights0166
    checked0166.1 checked0166.2.1 checked0166.2.2.1 checked0166.2.2.2
    (power_identity10 plusWeights0166) (power_identity10 minusWeights0166) g hg hmax

def envelope0166 : Envelope := ⟨coefficients0166, upper0166, bound0166⟩

def coefficients0167 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-5/1024), (-75/8192), (-15/4096), (-305/32768), (-275/65536)]

def upper0167 : ℚ := (30643/5242880000000)

def plusWeights0167 : Fin 11 → ℚ := ![(30643/5242880000000), (30643/524288000000), (275787/1048576000000), (91929/131072000000), (643503/524288000000), (1930509/1310720000000), (640943/524288000000), (89249/131072000000), (1210743/5242880000000), (472993/13107200000000), 0]

def minusWeights0167 : Fin 11 → ℚ := ![(30643/5242880000000), (30643/524288000000), (275787/1048576000000), (91929/131072000000), (643503/524288000000), (1930509/1310720000000), (646063/524288000000), (94609/131072000000), (1547127/5242880000000), (1059157/13107200000000), (30643/2621440000000)]

theorem checked0167 :
    (∀ i, 0 ≤ plusWeights0167 i) ∧
    (∀ i, 0 ≤ minusWeights0167 i) ∧
    (∀ i, plusCoefficients coefficients0167 upper0167 i = powerCoefficients10 plusWeights0167 i) ∧
    (∀ i, minusCoefficients coefficients0167 upper0167 i = powerCoefficients10 minusWeights0167 i) := by
  decide +kernel

theorem bound0167 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0167 g| ≤ (upper0167 : ℝ) :=
  abs_of_coefficients coefficients0167 upper0167 powerCoefficients10 plusWeights0167 minusWeights0167
    checked0167.1 checked0167.2.1 checked0167.2.2.1 checked0167.2.2.2
    (power_identity10 plusWeights0167) (power_identity10 minusWeights0167) g hg hmax

def envelope0167 : Envelope := ⟨coefficients0167, upper0167, bound0167⟩

def coefficients0168 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-279/2048), (-33/1024), (-2379/16384), (-2223/32768)]

def upper0168 : ℚ := (4619403/327680000000000)

def plusWeights0168 : Fin 11 → ℚ := ![(4619403/327680000000000), (4619403/32768000000000), (41574627/65536000000000), (13858209/8192000000000), (97007463/32768000000000), (291022389/81920000000000), (97007463/32768000000000), (13746609/8192000000000), (38875107/65536000000000), (130173/1310720000000), 0]

def minusWeights0168 : Fin 11 → ℚ := ![(4619403/327680000000000), (4619403/32768000000000), (41574627/65536000000000), (13858209/8192000000000), (97007463/32768000000000), (291022389/81920000000000), (97007463/32768000000000), (13969809/8192000000000), (44274147/65536000000000), (5984481/32768000000000), (4619403/163840000000000)]

theorem checked0168 :
    (∀ i, 0 ≤ plusWeights0168 i) ∧
    (∀ i, 0 ≤ minusWeights0168 i) ∧
    (∀ i, plusCoefficients coefficients0168 upper0168 i = powerCoefficients10 plusWeights0168 i) ∧
    (∀ i, minusCoefficients coefficients0168 upper0168 i = powerCoefficients10 minusWeights0168 i) := by
  decide +kernel

theorem bound0168 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0168 g| ≤ (upper0168 : ℝ) :=
  abs_of_coefficients coefficients0168 upper0168 powerCoefficients10 plusWeights0168 minusWeights0168
    checked0168.1 checked0168.2.1 checked0168.2.2.1 checked0168.2.2.2
    (power_identity10 plusWeights0168) (power_identity10 minusWeights0168) g hg hmax

def envelope0168 : Envelope := ⟨coefficients0168, upper0168, bound0168⟩

def coefficients0169 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-501/4096), (-81/1024), (-2643/16384), (-2271/32768)]

def upper0169 : ℚ := (4322331/327680000000000)

def plusWeights0169 : Fin 11 → ℚ := ![(4322331/327680000000000), (4322331/32768000000000), (38900979/65536000000000), (12966993/8192000000000), (90768951/32768000000000), (272306853/81920000000000), (90768951/32768000000000), (12866793/8192000000000), (36444339/65536000000000), (612561/6553600000000), 0]

def minusWeights0169 : Fin 11 → ℚ := ![(4322331/327680000000000), (4322331/32768000000000), (38900979/65536000000000), (12966993/8192000000000), (90768951/32768000000000), (272306853/81920000000000), (90768951/32768000000000), (13067193/8192000000000), (41357619/65536000000000), (5581857/32768000000000), (4322331/163840000000000)]

theorem checked0169 :
    (∀ i, 0 ≤ plusWeights0169 i) ∧
    (∀ i, 0 ≤ minusWeights0169 i) ∧
    (∀ i, plusCoefficients coefficients0169 upper0169 i = powerCoefficients10 plusWeights0169 i) ∧
    (∀ i, minusCoefficients coefficients0169 upper0169 i = powerCoefficients10 minusWeights0169 i) := by
  decide +kernel

theorem bound0169 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0169 g| ≤ (upper0169 : ℝ) :=
  abs_of_coefficients coefficients0169 upper0169 powerCoefficients10 plusWeights0169 minusWeights0169
    checked0169.1 checked0169.2.1 checked0169.2.2.1 checked0169.2.2.2
    (power_identity10 plusWeights0169) (power_identity10 minusWeights0169) g hg hmax

def envelope0169 : Envelope := ⟨coefficients0169, upper0169, bound0169⟩

def coefficients0170 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-57/512), (-63/512), (-4023/16384), (-3471/32768)]

def upper0170 : ℚ := (4135131/327680000000000)

def plusWeights0170 : Fin 11 → ℚ := ![(4135131/327680000000000), (4135131/32768000000000), (37216179/65536000000000), (12405393/8192000000000), (86837751/32768000000000), (260513253/81920000000000), (86837751/32768000000000), (12314193/8192000000000), (34946739/65536000000000), (590409/6553600000000), 0]

def minusWeights0170 : Fin 11 → ℚ := ![(4135131/327680000000000), (4135131/32768000000000), (37216179/65536000000000), (12405393/8192000000000), (86837751/32768000000000), (260513253/81920000000000), (86837751/32768000000000), (12496593/8192000000000), (39485619/65536000000000), (5318217/32768000000000), (4135131/163840000000000)]

theorem checked0170 :
    (∀ i, 0 ≤ plusWeights0170 i) ∧
    (∀ i, 0 ≤ minusWeights0170 i) ∧
    (∀ i, plusCoefficients coefficients0170 upper0170 i = powerCoefficients10 plusWeights0170 i) ∧
    (∀ i, minusCoefficients coefficients0170 upper0170 i = powerCoefficients10 minusWeights0170 i) := by
  decide +kernel

theorem bound0170 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0170 g| ≤ (upper0170 : ℝ) :=
  abs_of_coefficients coefficients0170 upper0170 powerCoefficients10 plusWeights0170 minusWeights0170
    checked0170.1 checked0170.2.1 checked0170.2.2.1 checked0170.2.2.2
    (power_identity10 plusWeights0170) (power_identity10 minusWeights0170) g hg hmax

def envelope0170 : Envelope := ⟨coefficients0170, upper0170, bound0170⟩

def coefficients0171 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/2048), (675/8192), (675/16384), (7875/131072)]

def upper0171 : ℚ := (21213/2097152000000)

def plusWeights0171 : Fin 11 → ℚ := ![(21213/2097152000000), (21213/209715200000), (190917/419430400000), (63639/52428800000), (445473/209715200000), (1336419/524288000000), (445473/209715200000), (63063/52428800000), (887193/2097152000000), (366381/5242880000000), 0]

def minusWeights0171 : Fin 11 → ℚ := ![(21213/2097152000000), (21213/209715200000), (190917/419430400000), (63639/52428800000), (445473/209715200000), (1336419/524288000000), (445473/209715200000), (12843/10485760000), (1021977/2097152000000), (694269/5242880000000), (21213/1048576000000)]

theorem checked0171 :
    (∀ i, 0 ≤ plusWeights0171 i) ∧
    (∀ i, 0 ≤ minusWeights0171 i) ∧
    (∀ i, plusCoefficients coefficients0171 upper0171 i = powerCoefficients10 plusWeights0171 i) ∧
    (∀ i, minusCoefficients coefficients0171 upper0171 i = powerCoefficients10 minusWeights0171 i) := by
  decide +kernel

theorem bound0171 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0171 g| ≤ (upper0171 : ℝ) :=
  abs_of_coefficients coefficients0171 upper0171 powerCoefficients10 plusWeights0171 minusWeights0171
    checked0171.1 checked0171.2.1 checked0171.2.2.1 checked0171.2.2.2
    (power_identity10 plusWeights0171) (power_identity10 minusWeights0171) g hg hmax

def envelope0171 : Envelope := ⟨coefficients0171, upper0171, bound0171⟩

def coefficients0172 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-111/1024), (-129/1024), (-3957/16384), (-3369/32768)]

def upper0172 : ℚ := (4047309/327680000000000)

def plusWeights0172 : Fin 11 → ℚ := ![(4047309/327680000000000), (4047309/32768000000000), (36425781/65536000000000), (12141927/8192000000000), (84993489/32768000000000), (254980467/81920000000000), (84993489/32768000000000), (12053127/8192000000000), (34212021/65536000000000), (578247/6553600000000), 0]

def minusWeights0172 : Fin 11 → ℚ := ![(4047309/327680000000000), (4047309/32768000000000), (36425781/65536000000000), (12141927/8192000000000), (84993489/32768000000000), (254980467/81920000000000), (84993489/32768000000000), (12230727/8192000000000), (38639541/65536000000000), (5203383/32768000000000), (4047309/163840000000000)]

theorem checked0172 :
    (∀ i, 0 ≤ plusWeights0172 i) ∧
    (∀ i, 0 ≤ minusWeights0172 i) ∧
    (∀ i, plusCoefficients coefficients0172 upper0172 i = powerCoefficients10 plusWeights0172 i) ∧
    (∀ i, minusCoefficients coefficients0172 upper0172 i = powerCoefficients10 minusWeights0172 i) := by
  decide +kernel

theorem bound0172 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0172 g| ≤ (upper0172 : ℝ) :=
  abs_of_coefficients coefficients0172 upper0172 powerCoefficients10 plusWeights0172 minusWeights0172
    checked0172.1 checked0172.2.1 checked0172.2.2.1 checked0172.2.2.2
    (power_identity10 plusWeights0172) (power_identity10 minusWeights0172) g hg hmax

def envelope0172 : Envelope := ⟨coefficients0172, upper0172, bound0172⟩

def coefficients0173 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-315/4096), (-45/2048), (-1665/16384), (-1575/32768)]

def upper0173 : ℚ := (4203/524288000000)

def plusWeights0173 : Fin 11 → ℚ := ![(4203/524288000000), (4203/52428800000), (37827/104857600000), (12609/13107200000), (88263/52428800000), (264789/131072000000), (88263/52428800000), (62541/65536000000), (884619/2621440000000), (370629/6553600000000), 0]

def minusWeights0173 : Fin 11 → ℚ := ![(4203/524288000000), (4203/52428800000), (37827/104857600000), (12609/13107200000), (88263/52428800000), (264789/131072000000), (88263/52428800000), (63549/65536000000), (1006731/2621440000000), (680121/6553600000000), (4203/262144000000)]

theorem checked0173 :
    (∀ i, 0 ≤ plusWeights0173 i) ∧
    (∀ i, 0 ≤ minusWeights0173 i) ∧
    (∀ i, plusCoefficients coefficients0173 upper0173 i = powerCoefficients10 plusWeights0173 i) ∧
    (∀ i, minusCoefficients coefficients0173 upper0173 i = powerCoefficients10 minusWeights0173 i) := by
  decide +kernel

theorem bound0173 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0173 g| ≤ (upper0173 : ℝ) :=
  abs_of_coefficients coefficients0173 upper0173 powerCoefficients10 plusWeights0173 minusWeights0173
    checked0173.1 checked0173.2.1 checked0173.2.2.1 checked0173.2.2.2
    (power_identity10 plusWeights0173) (power_identity10 minusWeights0173) g hg hmax

def envelope0173 : Envelope := ⟨coefficients0173, upper0173, bound0173⟩

def coefficients0174 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-315/4096), (-45/2048), (-915/16384), (-825/32768)]

def upper0174 : ℚ := (20889/2621440000000)

def plusWeights0174 : Fin 11 → ℚ := ![(20889/2621440000000), (20889/262144000000), (188001/524288000000), (62667/65536000000), (438669/262144000000), (1316007/655360000000), (438669/262144000000), (62163/65536000000), (878949/2621440000000), (367779/6553600000000), 0]

def minusWeights0174 : Fin 11 → ℚ := ![(20889/2621440000000), (20889/262144000000), (188001/524288000000), (62667/65536000000), (438669/262144000000), (1316007/655360000000), (438669/262144000000), (63171/65536000000), (1001061/2621440000000), (676671/6553600000000), (20889/1310720000000)]

theorem checked0174 :
    (∀ i, 0 ≤ plusWeights0174 i) ∧
    (∀ i, 0 ≤ minusWeights0174 i) ∧
    (∀ i, plusCoefficients coefficients0174 upper0174 i = powerCoefficients10 plusWeights0174 i) ∧
    (∀ i, minusCoefficients coefficients0174 upper0174 i = powerCoefficients10 minusWeights0174 i) := by
  decide +kernel

theorem bound0174 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0174 g| ≤ (upper0174 : ℝ) :=
  abs_of_coefficients coefficients0174 upper0174 powerCoefficients10 plusWeights0174 minusWeights0174
    checked0174.1 checked0174.2.1 checked0174.2.2.1 checked0174.2.2.2
    (power_identity10 plusWeights0174) (power_identity10 minusWeights0174) g hg hmax

def envelope0174 : Envelope := ⟨coefficients0174, upper0174, bound0174⟩

def coefficients0175 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-285/4096), (-15/1024), (-1185/16384), (-1125/32768)]

def upper0175 : ℚ := (94113/13107200000000)

def plusWeights0175 : Fin 11 → ℚ := ![(94113/13107200000000), (94113/1310720000000), (847017/2621440000000), (282339/327680000000), (1976373/1310720000000), (5929119/3276800000000), (1976373/1310720000000), (280059/327680000000), (791913/2621440000000), (331371/6553600000000), 0]

def minusWeights0175 : Fin 11 → ℚ := ![(94113/13107200000000), (94113/1310720000000), (847017/2621440000000), (282339/327680000000), (1976373/1310720000000), (5929119/3276800000000), (1976373/1310720000000), (284619/327680000000), (902121/2621440000000), (609759/6553600000000), (94113/6553600000000)]

theorem checked0175 :
    (∀ i, 0 ≤ plusWeights0175 i) ∧
    (∀ i, 0 ≤ minusWeights0175 i) ∧
    (∀ i, plusCoefficients coefficients0175 upper0175 i = powerCoefficients10 plusWeights0175 i) ∧
    (∀ i, minusCoefficients coefficients0175 upper0175 i = powerCoefficients10 minusWeights0175 i) := by
  decide +kernel

theorem bound0175 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0175 g| ≤ (upper0175 : ℝ) :=
  abs_of_coefficients coefficients0175 upper0175 powerCoefficients10 plusWeights0175 minusWeights0175
    checked0175.1 checked0175.2.1 checked0175.2.2.1 checked0175.2.2.2
    (power_identity10 plusWeights0175) (power_identity10 minusWeights0175) g hg hmax

def envelope0175 : Envelope := ⟨coefficients0175, upper0175, bound0175⟩

def coefficients0176 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-33/512), (-37/512), (-4609/32768), (-3953/65536)]

def upper0176 : ℚ := (4793733/655360000000000)

def plusWeights0176 : Fin 11 → ℚ := ![(4793733/655360000000000), (4793733/65536000000000), (43143597/131072000000000), (14381199/16384000000000), (100668393/65536000000000), (302005179/163840000000000), (100668393/65536000000000), (14275599/16384000000000), (40514477/131072000000000), (684519/13107200000000), 0]

def minusWeights0176 : Fin 11 → ℚ := ![(4793733/655360000000000), (4793733/65536000000000), (43143597/131072000000000), (14381199/16384000000000), (100668393/65536000000000), (302005179/163840000000000), (100668393/65536000000000), (14486799/16384000000000), (45772717/131072000000000), (6164871/65536000000000), (4793733/327680000000000)]

theorem checked0176 :
    (∀ i, 0 ≤ plusWeights0176 i) ∧
    (∀ i, 0 ≤ minusWeights0176 i) ∧
    (∀ i, plusCoefficients coefficients0176 upper0176 i = powerCoefficients10 plusWeights0176 i) ∧
    (∀ i, minusCoefficients coefficients0176 upper0176 i = powerCoefficients10 minusWeights0176 i) := by
  decide +kernel

theorem bound0176 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0176 g| ≤ (upper0176 : ℝ) :=
  abs_of_coefficients coefficients0176 upper0176 powerCoefficients10 plusWeights0176 minusWeights0176
    checked0176.1 checked0176.2.1 checked0176.2.2.1 checked0176.2.2.2
    (power_identity10 plusWeights0176) (power_identity10 minusWeights0176) g hg hmax

def envelope0176 : Envelope := ⟨coefficients0176, upper0176, bound0176⟩

def coefficients0177 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-1/16), (-19/256), (-3521/32768), (-2817/65536)]

def upper0177 : ℚ := (4655637/655360000000000)

def plusWeights0177 : Fin 11 → ℚ := ![(4655637/655360000000000), (4655637/65536000000000), (41900733/131072000000000), (13966911/16384000000000), (97768377/65536000000000), (293305131/163840000000000), (97768377/65536000000000), (13864511/16384000000000), (39345853/131072000000000), (664503/13107200000000), 0]

def minusWeights0177 : Fin 11 → ℚ := ![(4655637/655360000000000), (4655637/65536000000000), (41900733/131072000000000), (13966911/16384000000000), (97768377/65536000000000), (293305131/163840000000000), (97768377/65536000000000), (14069311/16384000000000), (44455613/131072000000000), (5988759/65536000000000), (4655637/327680000000000)]

theorem checked0177 :
    (∀ i, 0 ≤ plusWeights0177 i) ∧
    (∀ i, 0 ≤ minusWeights0177 i) ∧
    (∀ i, plusCoefficients coefficients0177 upper0177 i = powerCoefficients10 plusWeights0177 i) ∧
    (∀ i, minusCoefficients coefficients0177 upper0177 i = powerCoefficients10 minusWeights0177 i) := by
  decide +kernel

theorem bound0177 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0177 g| ≤ (upper0177 : ℝ) :=
  abs_of_coefficients coefficients0177 upper0177 powerCoefficients10 plusWeights0177 minusWeights0177
    checked0177.1 checked0177.2.1 checked0177.2.2.1 checked0177.2.2.2
    (power_identity10 plusWeights0177) (power_identity10 minusWeights0177) g hg hmax

def envelope0177 : Envelope := ⟨coefficients0177, upper0177, bound0177⟩

def coefficients0178 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-57/1024), (-63/1024), (-987/8192), (-849/16384)]

def upper0178 : ℚ := (1033389/163840000000000)

def plusWeights0178 : Fin 11 → ℚ := ![(1033389/163840000000000), (1033389/16384000000000), (9300501/32768000000000), (3100167/4096000000000), (21701169/16384000000000), (65103507/40960000000000), (21701169/16384000000000), (3077367/4096000000000), (8733141/32768000000000), (147531/3276800000000), 0]

def minusWeights0178 : Fin 11 → ℚ := ![(1033389/163840000000000), (1033389/16384000000000), (9300501/32768000000000), (3100167/4096000000000), (21701169/16384000000000), (65103507/40960000000000), (21701169/16384000000000), (3122967/4096000000000), (9867861/32768000000000), (1329123/16384000000000), (1033389/81920000000000)]

theorem checked0178 :
    (∀ i, 0 ≤ plusWeights0178 i) ∧
    (∀ i, 0 ≤ minusWeights0178 i) ∧
    (∀ i, plusCoefficients coefficients0178 upper0178 i = powerCoefficients10 plusWeights0178 i) ∧
    (∀ i, minusCoefficients coefficients0178 upper0178 i = powerCoefficients10 minusWeights0178 i) := by
  decide +kernel

theorem bound0178 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0178 g| ≤ (upper0178 : ℝ) :=
  abs_of_coefficients coefficients0178 upper0178 powerCoefficients10 plusWeights0178 minusWeights0178
    checked0178.1 checked0178.2.1 checked0178.2.2.1 checked0178.2.2.2
    (power_identity10 plusWeights0178) (power_identity10 minusWeights0178) g hg hmax

def envelope0178 : Envelope := ⟨coefficients0178, upper0178, bound0178⟩

def coefficients0179 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-57/1024), (-63/1024), (-57/512), (-387/8192)]

def upper0179 : ℚ := (515907/81920000000000)

def plusWeights0179 : Fin 11 → ℚ := ![(515907/81920000000000), (515907/8192000000000), (4643163/16384000000000), (1547721/2048000000000), (10834047/8192000000000), (32502141/20480000000000), (10834047/8192000000000), (1536321/2048000000000), (4359483/16384000000000), (73623/1638400000000), 0]

def minusWeights0179 : Fin 11 → ℚ := ![(515907/81920000000000), (515907/8192000000000), (4643163/16384000000000), (1547721/2048000000000), (10834047/8192000000000), (32502141/20480000000000), (10834047/8192000000000), (1559121/2048000000000), (4926843/16384000000000), (663699/8192000000000), (515907/40960000000000)]

theorem checked0179 :
    (∀ i, 0 ≤ plusWeights0179 i) ∧
    (∀ i, 0 ≤ minusWeights0179 i) ∧
    (∀ i, plusCoefficients coefficients0179 upper0179 i = powerCoefficients10 plusWeights0179 i) ∧
    (∀ i, minusCoefficients coefficients0179 upper0179 i = powerCoefficients10 minusWeights0179 i) := by
  decide +kernel

theorem bound0179 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0179 g| ≤ (upper0179 : ℝ) :=
  abs_of_coefficients coefficients0179 upper0179 powerCoefficients10 plusWeights0179 minusWeights0179
    checked0179.1 checked0179.2.1 checked0179.2.2.1 checked0179.2.2.2
    (power_identity10 plusWeights0179) (power_identity10 minusWeights0179) g hg hmax

def envelope0179 : Envelope := ⟨coefficients0179, upper0179, bound0179⟩

def coefficients0180 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-57/1024), (-63/1024), (-837/8192), (-699/16384)]

def upper0180 : ℚ := (1030239/163840000000000)

def plusWeights0180 : Fin 11 → ℚ := ![(1030239/163840000000000), (1030239/16384000000000), (9272151/32768000000000), (3090717/4096000000000), (21635019/16384000000000), (64905057/40960000000000), (21635019/16384000000000), (3067917/4096000000000), (8704791/32768000000000), (146961/3276800000000), 0]

def minusWeights0180 : Fin 11 → ℚ := ![(1030239/163840000000000), (1030239/16384000000000), (9272151/32768000000000), (3090717/4096000000000), (21635019/16384000000000), (64905057/40960000000000), (21635019/16384000000000), (3113517/4096000000000), (9839511/32768000000000), (1325673/16384000000000), (1030239/81920000000000)]

theorem checked0180 :
    (∀ i, 0 ≤ plusWeights0180 i) ∧
    (∀ i, 0 ≤ minusWeights0180 i) ∧
    (∀ i, plusCoefficients coefficients0180 upper0180 i = powerCoefficients10 plusWeights0180 i) ∧
    (∀ i, minusCoefficients coefficients0180 upper0180 i = powerCoefficients10 minusWeights0180 i) := by
  decide +kernel

theorem bound0180 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0180 g| ≤ (upper0180 : ℝ) :=
  abs_of_coefficients coefficients0180 upper0180 powerCoefficients10 plusWeights0180 minusWeights0180
    checked0180.1 checked0180.2.1 checked0180.2.2.1 checked0180.2.2.2
    (power_identity10 plusWeights0180) (power_identity10 minusWeights0180) g hg hmax

def envelope0180 : Envelope := ⟨coefficients0180, upper0180, bound0180⟩

def coefficients0181 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-57/1024), (-63/1024), (-537/8192), (-399/16384)]

def upper0181 : ℚ := (1023939/163840000000000)

def plusWeights0181 : Fin 11 → ℚ := ![(1023939/163840000000000), (1023939/16384000000000), (9215451/32768000000000), (3071817/4096000000000), (21502719/16384000000000), (64508157/40960000000000), (21502719/16384000000000), (3049017/4096000000000), (8648091/32768000000000), (145821/3276800000000), 0]

def minusWeights0181 : Fin 11 → ℚ := ![(1023939/163840000000000), (1023939/16384000000000), (9215451/32768000000000), (3071817/4096000000000), (21502719/16384000000000), (64508157/40960000000000), (21502719/16384000000000), (3094617/4096000000000), (9782811/32768000000000), (1318773/16384000000000), (1023939/81920000000000)]

theorem checked0181 :
    (∀ i, 0 ≤ plusWeights0181 i) ∧
    (∀ i, 0 ≤ minusWeights0181 i) ∧
    (∀ i, plusCoefficients coefficients0181 upper0181 i = powerCoefficients10 plusWeights0181 i) ∧
    (∀ i, minusCoefficients coefficients0181 upper0181 i = powerCoefficients10 minusWeights0181 i) := by
  decide +kernel

theorem bound0181 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0181 g| ≤ (upper0181 : ℝ) :=
  abs_of_coefficients coefficients0181 upper0181 powerCoefficients10 plusWeights0181 minusWeights0181
    checked0181.1 checked0181.2.1 checked0181.2.2.1 checked0181.2.2.2
    (power_identity10 plusWeights0181) (power_identity10 minusWeights0181) g hg hmax

def envelope0181 : Envelope := ⟨coefficients0181, upper0181, bound0181⟩

def coefficients0182 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-57/1024), (-63/1024), (-231/4096), (-81/4096)]

def upper0182 : ℚ := (255591/40960000000000)

def plusWeights0182 : Fin 11 → ℚ := ![(255591/40960000000000), (255591/4096000000000), (2300319/8192000000000), (766773/1024000000000), (5367411/4096000000000), (16102233/10240000000000), (5367411/4096000000000), (761073/1024000000000), (2158479/8192000000000), (1137/25600000000), 0]

def minusWeights0182 : Fin 11 → ℚ := ![(255591/40960000000000), (255591/4096000000000), (2300319/8192000000000), (766773/1024000000000), (5367411/4096000000000), (16102233/10240000000000), (5367411/4096000000000), (772473/1024000000000), (2442159/8192000000000), (164631/2048000000000), (255591/20480000000000)]

theorem checked0182 :
    (∀ i, 0 ≤ plusWeights0182 i) ∧
    (∀ i, 0 ≤ minusWeights0182 i) ∧
    (∀ i, plusCoefficients coefficients0182 upper0182 i = powerCoefficients10 plusWeights0182 i) ∧
    (∀ i, minusCoefficients coefficients0182 upper0182 i = powerCoefficients10 minusWeights0182 i) := by
  decide +kernel

theorem bound0182 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0182 g| ≤ (upper0182 : ℝ) :=
  abs_of_coefficients coefficients0182 upper0182 powerCoefficients10 plusWeights0182 minusWeights0182
    checked0182.1 checked0182.2.1 checked0182.2.2.1 checked0182.2.2.2
    (power_identity10 plusWeights0182) (power_identity10 minusWeights0182) g hg hmax

def envelope0182 : Envelope := ⟨coefficients0182, upper0182, bound0182⟩

def coefficients0183 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/4096), (525/16384), (525/32768), (2625/262144)]

def upper0183 : ℚ := (108123/20971520000000)

def plusWeights0183 : Fin 11 → ℚ := ![(108123/20971520000000), (108123/2097152000000), (973107/4194304000000), (324369/524288000000), (2270583/2097152000000), (6811749/5242880000000), (2270583/2097152000000), (321489/524288000000), (905331/4194304000000), (374703/10485760000000), 0]

def minusWeights0183 : Fin 11 → ℚ := ![(108123/20971520000000), (108123/2097152000000), (973107/4194304000000), (324369/524288000000), (2270583/2097152000000), (6811749/5242880000000), (2270583/2097152000000), (327249/524288000000), (1040883/4194304000000), (706527/10485760000000), (108123/10485760000000)]

theorem checked0183 :
    (∀ i, 0 ≤ plusWeights0183 i) ∧
    (∀ i, 0 ≤ minusWeights0183 i) ∧
    (∀ i, plusCoefficients coefficients0183 upper0183 i = powerCoefficients10 plusWeights0183 i) ∧
    (∀ i, minusCoefficients coefficients0183 upper0183 i = powerCoefficients10 minusWeights0183 i) := by
  decide +kernel

theorem bound0183 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0183 g| ≤ (upper0183 : ℝ) :=
  abs_of_coefficients coefficients0183 upper0183 powerCoefficients10 plusWeights0183 minusWeights0183
    checked0183.1 checked0183.2.1 checked0183.2.2.1 checked0183.2.2.2
    (power_identity10 plusWeights0183) (power_identity10 minusWeights0183) g hg hmax

def envelope0183 : Envelope := ⟨coefficients0183, upper0183, bound0183⟩

def coefficients0184 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-225/4096), (1575/16384), (1575/32768), (7875/131072)]

def upper0184 : ℚ := (46953/10485760000000)

def plusWeights0184 : Fin 11 → ℚ := ![(46953/10485760000000), (46953/1048576000000), (422577/2097152000000), (140859/262144000000), (986013/1048576000000), (2958039/2621440000000), (986013/1048576000000), (139419/262144000000), (390033/2097152000000), (158697/5242880000000), 0]

def minusWeights0184 : Fin 11 → ℚ := ![(46953/10485760000000), (46953/1048576000000), (422577/2097152000000), (140859/262144000000), (986013/1048576000000), (2958039/2621440000000), (986013/1048576000000), (142299/262144000000), (455121/2097152000000), (310833/5242880000000), (46953/5242880000000)]

theorem checked0184 :
    (∀ i, 0 ≤ plusWeights0184 i) ∧
    (∀ i, 0 ≤ minusWeights0184 i) ∧
    (∀ i, plusCoefficients coefficients0184 upper0184 i = powerCoefficients10 plusWeights0184 i) ∧
    (∀ i, minusCoefficients coefficients0184 upper0184 i = powerCoefficients10 minusWeights0184 i) := by
  decide +kernel

theorem bound0184 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0184 g| ≤ (upper0184 : ℝ) :=
  abs_of_coefficients coefficients0184 upper0184 powerCoefficients10 plusWeights0184 minusWeights0184
    checked0184.1 checked0184.2.1 checked0184.2.2.1 checked0184.2.2.2
    (power_identity10 plusWeights0184) (power_identity10 minusWeights0184) g hg hmax

def envelope0184 : Envelope := ⟨coefficients0184, upper0184, bound0184⟩

def coefficients0185 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/512), (-33/512), (-729/8192), (-573/16384)]

def upper0185 : ℚ := (984753/163840000000000)

def plusWeights0185 : Fin 11 → ℚ := ![(984753/163840000000000), (984753/16384000000000), (8862777/32768000000000), (2954259/4096000000000), (20679813/16384000000000), (62039439/40960000000000), (20679813/16384000000000), (2932659/4096000000000), (8323257/32768000000000), (28119/655360000000), 0]

def minusWeights0185 : Fin 11 → ℚ := ![(984753/163840000000000), (984753/16384000000000), (8862777/32768000000000), (2954259/4096000000000), (20679813/16384000000000), (62039439/40960000000000), (20679813/16384000000000), (2975859/4096000000000), (9402297/32768000000000), (1266531/16384000000000), (984753/81920000000000)]

theorem checked0185 :
    (∀ i, 0 ≤ plusWeights0185 i) ∧
    (∀ i, 0 ≤ minusWeights0185 i) ∧
    (∀ i, plusCoefficients coefficients0185 upper0185 i = powerCoefficients10 plusWeights0185 i) ∧
    (∀ i, minusCoefficients coefficients0185 upper0185 i = powerCoefficients10 minusWeights0185 i) := by
  decide +kernel

theorem bound0185 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0185 g| ≤ (upper0185 : ℝ) :=
  abs_of_coefficients coefficients0185 upper0185 powerCoefficients10 plusWeights0185 minusWeights0185
    checked0185.1 checked0185.2.1 checked0185.2.2.1 checked0185.2.2.2
    (power_identity10 plusWeights0185) (power_identity10 minusWeights0185) g hg hmax

def envelope0185 : Envelope := ⟨coefficients0185, upper0185, bound0185⟩

def coefficients0186 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-27/512), (-33/512), (-327/4096), (-249/8192)]

def upper0186 : ℚ := (491589/81920000000000)

def plusWeights0186 : Fin 11 → ℚ := ![(491589/81920000000000), (491589/8192000000000), (4424301/16384000000000), (1474767/2048000000000), (10323369/8192000000000), (30970107/20480000000000), (10323369/8192000000000), (1463967/2048000000000), (4154541/16384000000000), (14031/327680000000), 0]

def minusWeights0186 : Fin 11 → ℚ := ![(491589/81920000000000), (491589/8192000000000), (4424301/16384000000000), (1474767/2048000000000), (10323369/8192000000000), (30970107/20480000000000), (10323369/8192000000000), (1485567/2048000000000), (4694061/16384000000000), (632403/8192000000000), (491589/40960000000000)]

theorem checked0186 :
    (∀ i, 0 ≤ plusWeights0186 i) ∧
    (∀ i, 0 ≤ minusWeights0186 i) ∧
    (∀ i, plusCoefficients coefficients0186 upper0186 i = powerCoefficients10 plusWeights0186 i) ∧
    (∀ i, minusCoefficients coefficients0186 upper0186 i = powerCoefficients10 minusWeights0186 i) := by
  decide +kernel

theorem bound0186 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0186 g| ≤ (upper0186 : ℝ) :=
  abs_of_coefficients coefficients0186 upper0186 powerCoefficients10 plusWeights0186 minusWeights0186
    checked0186.1 checked0186.2.1 checked0186.2.2.1 checked0186.2.2.2
    (power_identity10 plusWeights0186) (power_identity10 minusWeights0186) g hg hmax

def envelope0186 : Envelope := ⟨coefficients0186, upper0186, bound0186⟩

def coefficients0187 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-205/4096), (5/1024), (-1635/32768), (-1675/65536)]

def upper0187 : ℚ := (26259/5242880000000)

def plusWeights0187 : Fin 11 → ℚ := ![(26259/5242880000000), (26259/524288000000), (236331/1048576000000), (78777/131072000000), (551439/524288000000), (1654317/1310720000000), (551439/524288000000), (78121/131072000000), (1103191/5242880000000), (460301/13107200000000), 0]

def minusWeights0187 : Fin 11 → ℚ := ![(26259/5242880000000), (26259/524288000000), (236331/1048576000000), (78777/131072000000), (551439/524288000000), (1654317/1310720000000), (551439/524288000000), (79433/131072000000), (1260119/5242880000000), (852649/13107200000000), (26259/2621440000000)]

theorem checked0187 :
    (∀ i, 0 ≤ plusWeights0187 i) ∧
    (∀ i, 0 ≤ minusWeights0187 i) ∧
    (∀ i, plusCoefficients coefficients0187 upper0187 i = powerCoefficients10 plusWeights0187 i) ∧
    (∀ i, minusCoefficients coefficients0187 upper0187 i = powerCoefficients10 minusWeights0187 i) := by
  decide +kernel

theorem bound0187 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0187 g| ≤ (upper0187 : ℝ) :=
  abs_of_coefficients coefficients0187 upper0187 powerCoefficients10 plusWeights0187 minusWeights0187
    checked0187.1 checked0187.2.1 checked0187.2.2.1 checked0187.2.2.2
    (power_identity10 plusWeights0187) (power_identity10 minusWeights0187) g hg hmax

def envelope0187 : Envelope := ⟨coefficients0187, upper0187, bound0187⟩

def coefficients0188 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-393/8192), (-3/128), (-2589/32768), (-2373/65536)]

def upper0188 : ℚ := (3351753/655360000000000)

def plusWeights0188 : Fin 11 → ℚ := ![(3351753/655360000000000), (3351753/65536000000000), (30165777/131072000000000), (10055259/16384000000000), (70386813/65536000000000), (211160439/163840000000000), (70386813/65536000000000), (9976659/16384000000000), (28248657/131072000000000), (474531/13107200000000), 0]

def minusWeights0188 : Fin 11 → ℚ := ![(3351753/655360000000000), (3351753/65536000000000), (30165777/131072000000000), (10055259/16384000000000), (70386813/65536000000000), (211160439/163840000000000), (70386813/65536000000000), (10133859/16384000000000), (32082897/131072000000000), (4330851/65536000000000), (3351753/327680000000000)]

theorem checked0188 :
    (∀ i, 0 ≤ plusWeights0188 i) ∧
    (∀ i, 0 ≤ minusWeights0188 i) ∧
    (∀ i, plusCoefficients coefficients0188 upper0188 i = powerCoefficients10 plusWeights0188 i) ∧
    (∀ i, minusCoefficients coefficients0188 upper0188 i = powerCoefficients10 minusWeights0188 i) := by
  decide +kernel

theorem bound0188 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0188 g| ≤ (upper0188 : ℝ) :=
  abs_of_coefficients coefficients0188 upper0188 powerCoefficients10 plusWeights0188 minusWeights0188
    checked0188.1 checked0188.2.1 checked0188.2.2.1 checked0188.2.2.2
    (power_identity10 plusWeights0188) (power_identity10 minusWeights0188) g hg hmax

def envelope0188 : Envelope := ⟨coefficients0188, upper0188, bound0188⟩

def coefficients0189 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-45/1024), (-45/1024), (-1455/16384), (-1275/32768)]

def upper0189 : ℚ := (2583/524288000000)

def plusWeights0189 : Fin 11 → ℚ := ![(2583/524288000000), (2583/52428800000), (23247/104857600000), (7749/13107200000), (54243/52428800000), (162729/131072000000), (54243/52428800000), (38457/65536000000), (545463/2621440000000), (230133/6553600000000), 0]

def minusWeights0189 : Fin 11 → ℚ := ![(2583/524288000000), (2583/52428800000), (23247/104857600000), (7749/13107200000), (54243/52428800000), (162729/131072000000), (54243/52428800000), (39033/65536000000), (616887/2621440000000), (415617/6553600000000), (2583/262144000000)]

theorem checked0189 :
    (∀ i, 0 ≤ plusWeights0189 i) ∧
    (∀ i, 0 ≤ minusWeights0189 i) ∧
    (∀ i, plusCoefficients coefficients0189 upper0189 i = powerCoefficients10 plusWeights0189 i) ∧
    (∀ i, minusCoefficients coefficients0189 upper0189 i = powerCoefficients10 minusWeights0189 i) := by
  decide +kernel

theorem bound0189 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0189 g| ≤ (upper0189 : ℝ) :=
  abs_of_coefficients coefficients0189 upper0189 powerCoefficients10 plusWeights0189 minusWeights0189
    checked0189.1 checked0189.2.1 checked0189.2.2.1 checked0189.2.2.2
    (power_identity10 plusWeights0189) (power_identity10 minusWeights0189) g hg hmax

def envelope0189 : Envelope := ⟨coefficients0189, upper0189, bound0189⟩

def coefficients0190 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/128), (-5/128), (-205/8192), (-125/16384)]

def upper0190 : ℚ := (28329/6553600000000)

def plusWeights0190 : Fin 11 → ℚ := ![(28329/6553600000000), (28329/655360000000), (254961/1310720000000), (84987/163840000000), (594909/655360000000), (1784727/1638400000000), (594909/655360000000), (84347/163840000000), (239089/1310720000000), (100603/3276800000000), 0]

def minusWeights0190 : Fin 11 → ℚ := ![(28329/6553600000000), (28329/655360000000), (254961/1310720000000), (84987/163840000000), (594909/655360000000), (1784727/1638400000000), (594909/655360000000), (85627/163840000000), (270833/1310720000000), (182687/3276800000000), (28329/3276800000000)]

theorem checked0190 :
    (∀ i, 0 ≤ plusWeights0190 i) ∧
    (∀ i, 0 ≤ minusWeights0190 i) ∧
    (∀ i, plusCoefficients coefficients0190 upper0190 i = powerCoefficients10 plusWeights0190 i) ∧
    (∀ i, minusCoefficients coefficients0190 upper0190 i = powerCoefficients10 minusWeights0190 i) := by
  decide +kernel

theorem bound0190 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0190 g| ≤ (upper0190 : ℝ) :=
  abs_of_coefficients coefficients0190 upper0190 powerCoefficients10 plusWeights0190 minusWeights0190
    checked0190.1 checked0190.2.1 checked0190.2.2.1 checked0190.2.2.2
    (power_identity10 plusWeights0190) (power_identity10 minusWeights0190) g hg hmax

def envelope0190 : Envelope := ⟨coefficients0190, upper0190, bound0190⟩

def coefficients0191 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-315/8192), (-45/4096), (-1065/32768), (-975/65536)]

def upper0191 : ℚ := (104571/26214400000000)

def plusWeights0191 : Fin 11 → ℚ := ![(104571/26214400000000), (104571/2621440000000), (941139/5242880000000), (313713/655360000000), (2195991/2621440000000), (6587973/6553600000000), (2195991/2621440000000), (311193/655360000000), (880083/5242880000000), (368349/13107200000000), 0]

def minusWeights0191 : Fin 11 → ℚ := ![(104571/26214400000000), (104571/2621440000000), (941139/5242880000000), (313713/655360000000), (2195991/2621440000000), (6587973/6553600000000), (2195991/2621440000000), (316233/655360000000), (200439/1048576000000), (677361/13107200000000), (104571/13107200000000)]

theorem checked0191 :
    (∀ i, 0 ≤ plusWeights0191 i) ∧
    (∀ i, 0 ≤ minusWeights0191 i) ∧
    (∀ i, plusCoefficients coefficients0191 upper0191 i = powerCoefficients10 plusWeights0191 i) ∧
    (∀ i, minusCoefficients coefficients0191 upper0191 i = powerCoefficients10 minusWeights0191 i) := by
  decide +kernel

theorem bound0191 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0191 g| ≤ (upper0191 : ℝ) :=
  abs_of_coefficients coefficients0191 upper0191 powerCoefficients10 plusWeights0191 minusWeights0191
    checked0191.1 checked0191.2.1 checked0191.2.2.1 checked0191.2.2.2
    (power_identity10 plusWeights0191) (power_identity10 minusWeights0191) g hg hmax

def envelope0191 : Envelope := ⟨coefficients0191, upper0191, bound0191⟩

end BilayerDressed.CubicQuarticEnvelopes

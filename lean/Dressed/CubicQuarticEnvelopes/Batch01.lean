import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0032 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/4), (369/1024), (101/512), (3/16), (95/2048)]

def upper0032 : ℚ := (1180467/4096000000000)

def plusWeights0032 : Fin 11 → ℚ := ![(1180467/4096000000000), (1180467/409600000000), (10624203/819200000000), (3541401/102400000000), (24789807/409600000000), (74369421/1024000000000), (24892207/409600000000), (3647491/102400000000), (11943179/819200000000), (8180199/2048000000000), (1180467/2048000000000)]

def minusWeights0032 : Fin 11 → ℚ := ![(1180467/4096000000000), (1180467/409600000000), (10624203/819200000000), (3541401/102400000000), (24789807/409600000000), (74369421/1024000000000), (24687407/409600000000), (3435311/102400000000), (9305227/819200000000), (3624471/2048000000000), 0]

theorem checked0032 :
    (∀ i, 0 ≤ plusWeights0032 i) ∧
    (∀ i, 0 ≤ minusWeights0032 i) ∧
    (∀ i, plusCoefficients coefficients0032 upper0032 i = powerCoefficients10 plusWeights0032 i) ∧
    (∀ i, minusCoefficients coefficients0032 upper0032 i = powerCoefficients10 minusWeights0032 i) := by
  decide +kernel

theorem bound0032 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0032 g| ≤ (upper0032 : ℝ) :=
  abs_of_coefficients coefficients0032 upper0032 powerCoefficients10 plusWeights0032 minusWeights0032
    checked0032.1 checked0032.2.1 checked0032.2.2.1 checked0032.2.2.2
    (power_identity10 plusWeights0032) (power_identity10 minusWeights0032) g hg hmax

def envelope0032 : Envelope := ⟨coefficients0032, upper0032, bound0032⟩

def coefficients0033 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/32), (53/256), (1/8), (2835/8192), (4155/16384), (21255/65536)]

def upper0033 : ℚ := (70225491/131072000000000)

def plusWeights0033 : Fin 11 → ℚ := ![(70225491/131072000000000), (70225491/13107200000000), (632029419/26214400000000), (210676473/3276800000000), (1474735311/13107200000000), (4434445933/32768000000000), (1497928911/13107200000000), (223671033/3276800000000), (747586379/26214400000000), (20429091/2621440000000), (70225491/65536000000000)]

def minusWeights0033 : Fin 11 → ℚ := ![(70225491/131072000000000), (70225491/13107200000000), (632029419/26214400000000), (210676473/3276800000000), (1474735311/13107200000000), (4413965933/32768000000000), (1451541711/13107200000000), (197681913/3276800000000), (516472459/26214400000000), (38305527/13107200000000), 0]

theorem checked0033 :
    (∀ i, 0 ≤ plusWeights0033 i) ∧
    (∀ i, 0 ≤ minusWeights0033 i) ∧
    (∀ i, plusCoefficients coefficients0033 upper0033 i = powerCoefficients10 plusWeights0033 i) ∧
    (∀ i, minusCoefficients coefficients0033 upper0033 i = powerCoefficients10 minusWeights0033 i) := by
  decide +kernel

theorem bound0033 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0033 g| ≤ (upper0033 : ℝ) :=
  abs_of_coefficients coefficients0033 upper0033 powerCoefficients10 plusWeights0033 minusWeights0033
    checked0033.1 checked0033.2.1 checked0033.2.2.1 checked0033.2.2.2
    (power_identity10 plusWeights0033) (power_identity10 minusWeights0033) g hg hmax

def envelope0033 : Envelope := ⟨coefficients0033, upper0033, bound0033⟩

def coefficients0034 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/16), (53/128), (1/4), (1215/4096), (1815/8192), (1815/32768)]

def upper0034 : ℚ := (69943683/65536000000000)

def plusWeights0034 : Fin 11 → ℚ := ![(69943683/65536000000000), (69943683/6553600000000), (629493147/13107200000000), (209831049/1638400000000), (1468817343/6553600000000), (4416692029/16384000000000), (1492010943/6553600000000), (222825609/1638400000000), (744998267/13107200000000), (20361987/1310720000000), (69943683/32768000000000)]

def minusWeights0034 : Fin 11 → ℚ := ![(69943683/65536000000000), (69943683/6553600000000), (629493147/13107200000000), (209831049/1638400000000), (1468817343/6553600000000), (4396212029/16384000000000), (1445623743/6553600000000), (196836489/1638400000000), (513988027/13107200000000), (38077431/6553600000000), 0]

theorem checked0034 :
    (∀ i, 0 ≤ plusWeights0034 i) ∧
    (∀ i, 0 ≤ minusWeights0034 i) ∧
    (∀ i, plusCoefficients coefficients0034 upper0034 i = powerCoefficients10 plusWeights0034 i) ∧
    (∀ i, minusCoefficients coefficients0034 upper0034 i = powerCoefficients10 minusWeights0034 i) := by
  decide +kernel

theorem bound0034 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0034 g| ≤ (upper0034 : ℝ) :=
  abs_of_coefficients coefficients0034 upper0034 powerCoefficients10 plusWeights0034 minusWeights0034
    checked0034.1 checked0034.2.1 checked0034.2.2.1 checked0034.2.2.2
    (power_identity10 plusWeights0034) (power_identity10 minusWeights0034) g hg hmax

def envelope0034 : Envelope := ⟨coefficients0034, upper0034, bound0034⟩

def coefficients0035 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (15/128), (57/256), (207/1024), (39/256), (63/512), (15/512)]

def upper0035 : ℚ := (1450389/1024000000000)

def plusWeights0035 : Fin 11 → ℚ := ![(1450389/1024000000000), (1450389/102400000000), (13053501/204800000000), (4351167/25600000000), (30458169/102400000000), (91674507/256000000000), (31080969/102400000000), (9348969/51200000000), (15739833/204800000000), (5370309/256000000000), (1450389/512000000000)]

def minusWeights0035 : Fin 11 → ℚ := ![(1450389/1024000000000), (1450389/102400000000), (13053501/204800000000), (4351167/25600000000), (30458169/102400000000), (91074507/256000000000), (29835369/102400000000), (8055699/51200000000), (10367169/204800000000), (470409/64000000000), 0]

theorem checked0035 :
    (∀ i, 0 ≤ plusWeights0035 i) ∧
    (∀ i, 0 ≤ minusWeights0035 i) ∧
    (∀ i, plusCoefficients coefficients0035 upper0035 i = powerCoefficients10 plusWeights0035 i) ∧
    (∀ i, minusCoefficients coefficients0035 upper0035 i = powerCoefficients10 minusWeights0035 i) := by
  decide +kernel

theorem bound0035 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0035 g| ≤ (upper0035 : ℝ) :=
  abs_of_coefficients coefficients0035 upper0035 powerCoefficients10 plusWeights0035 minusWeights0035
    checked0035.1 checked0035.2.1 checked0035.2.2.1 checked0035.2.2.2
    (power_identity10 plusWeights0035) (power_identity10 minusWeights0035) g hg hmax

def envelope0035 : Envelope := ⟨coefficients0035, upper0035, bound0035⟩

def coefficients0036 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-21/256), (-35/512), (-563/2048), (-255/1024), (-1923/8192), (-1371/16384)]

def upper0036 : ℚ := (361448169/163840000000000)

def plusWeights0036 : Fin 11 → ℚ := ![(361448169/163840000000000), (361448169/16384000000000), (3253033521/32768000000000), (1084344507/4096000000000), (7641611549/16384000000000), (23505634647/40960000000000), (8290091549/16384000000000), (1305511907/4096000000000), (4504009521/32768000000000), (595531523/16384000000000), (361448169/81920000000000)]

def minusWeights0036 : Fin 11 → ℚ := ![(361448169/163840000000000), (361448169/16384000000000), (3253033521/32768000000000), (1084344507/4096000000000), (7539211549/16384000000000), (22036834647/40960000000000), (6890731549/16384000000000), (863177107/4096000000000), (2002057521/32768000000000), (25472963/3276800000000), 0]

theorem checked0036 :
    (∀ i, 0 ≤ plusWeights0036 i) ∧
    (∀ i, 0 ≤ minusWeights0036 i) ∧
    (∀ i, plusCoefficients coefficients0036 upper0036 i = powerCoefficients10 plusWeights0036 i) ∧
    (∀ i, minusCoefficients coefficients0036 upper0036 i = powerCoefficients10 minusWeights0036 i) := by
  decide +kernel

theorem bound0036 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0036 g| ≤ (upper0036 : ℝ) :=
  abs_of_coefficients coefficients0036 upper0036 powerCoefficients10 plusWeights0036 minusWeights0036
    checked0036.1 checked0036.2.1 checked0036.2.2.1 checked0036.2.2.2
    (power_identity10 plusWeights0036) (power_identity10 minusWeights0036) g hg hmax

def envelope0036 : Envelope := ⟨coefficients0036, upper0036, bound0036⟩

def coefficients0037 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-19/256), (-37/512), (-427/2048), (-39/256), (-225/2048), (-75/2048)]

def upper0037 : ℚ := (1874379/819200000000)

def plusWeights0037 : Fin 11 → ℚ := ![(1874379/819200000000), (1874379/81920000000), (16869411/163840000000), (5623137/20480000000), (39617959/81920000000), (121773877/204800000000), (42892039/81920000000), (674479/2048000000), (116259367/819200000000), (7693291/204800000000), (1874379/409600000000)]

def minusWeights0037 : Fin 11 → ℚ := ![(1874379/819200000000), (1874379/81920000000), (16869411/163840000000), (5623137/20480000000), (39105959/81920000000), (114397877/204800000000), (35831879/81920000000), (1125371/5120000000), (52434743/819200000000), (419651/51200000000), 0]

theorem checked0037 :
    (∀ i, 0 ≤ plusWeights0037 i) ∧
    (∀ i, 0 ≤ minusWeights0037 i) ∧
    (∀ i, plusCoefficients coefficients0037 upper0037 i = powerCoefficients10 plusWeights0037 i) ∧
    (∀ i, minusCoefficients coefficients0037 upper0037 i = powerCoefficients10 minusWeights0037 i) := by
  decide +kernel

theorem bound0037 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0037 g| ≤ (upper0037 : ℝ) :=
  abs_of_coefficients coefficients0037 upper0037 powerCoefficients10 plusWeights0037 minusWeights0037
    checked0037.1 checked0037.2.1 checked0037.2.2.1 checked0037.2.2.2
    (power_identity10 plusWeights0037) (power_identity10 minusWeights0037) g hg hmax

def envelope0037 : Envelope := ⟨coefficients0037, upper0037, bound0037⟩

def coefficients0038 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/64), (-1/256), (35/256), (189/2048), (85/256), (855/4096), (7795/32768)]

def upper0038 : ℚ := (314437639/65536000000000)

def plusWeights0038 : Fin 11 → ℚ := ![(314437639/65536000000000), (314437639/6553600000000), (2829938751/13107200000000), (943312917/1638400000000), (6633910419/6553600000000), (20269731257/16384000000000), (7063606419/6553600000000), (1097184037/1638400000000), (3757577151/13107200000000), (501287967/6553600000000), (314437639/32768000000000)]

def minusWeights0038 : Fin 11 → ℚ := ![(314437639/65536000000000), (314437639/6553600000000), (2829938751/13107200000000), (943312917/1638400000000), (6572470419/6553600000000), (19349411257/16384000000000), (6142774419/6553600000000), (789441797/1638400000000), (1902300351/13107200000000), (127587311/6553600000000), 0]

theorem checked0038 :
    (∀ i, 0 ≤ plusWeights0038 i) ∧
    (∀ i, 0 ≤ minusWeights0038 i) ∧
    (∀ i, plusCoefficients coefficients0038 upper0038 i = powerCoefficients10 plusWeights0038 i) ∧
    (∀ i, minusCoefficients coefficients0038 upper0038 i = powerCoefficients10 minusWeights0038 i) := by
  decide +kernel

theorem bound0038 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0038 g| ≤ (upper0038 : ℝ) :=
  abs_of_coefficients coefficients0038 upper0038 powerCoefficients10 plusWeights0038 minusWeights0038
    checked0038.1 checked0038.2.1 checked0038.2.2.1 checked0038.2.2.2
    (power_identity10 plusWeights0038) (power_identity10 minusWeights0038) g hg hmax

def envelope0038 : Envelope := ⟨coefficients0038, upper0038, bound0038⟩

def coefficients0039 : Fin 11 → ℚ := ![0, 0, 0, 0, (7/128), (-25/256), (113/1024), (131/1024), (2755/8192), (2685/16384), (7425/65536)]

def upper0039 : ℚ := (121080913/26214400000000)

def plusWeights0039 : Fin 11 → ℚ := ![(121080913/26214400000000), (121080913/2621440000000), (1089728217/5242880000000), (363242739/655360000000), (2557035173/2621440000000), (7836737519/6553600000000), (2745228453/2621440000000), (428820403/655360000000), (58891937/209715200000), (977863513/13107200000000), (121080913/13107200000000)]

def minusWeights0039 : Fin 11 → ℚ := ![(121080913/26214400000000), (121080913/2621440000000), (1089728217/5242880000000), (363242739/655360000000), (2528363173/2621440000000), (7419457519/6553600000000), (2340169893/2621440000000), (11906603/26214400000), (707158009/5242880000000), (232945617/13107200000000), 0]

theorem checked0039 :
    (∀ i, 0 ≤ plusWeights0039 i) ∧
    (∀ i, 0 ≤ minusWeights0039 i) ∧
    (∀ i, plusCoefficients coefficients0039 upper0039 i = powerCoefficients10 plusWeights0039 i) ∧
    (∀ i, minusCoefficients coefficients0039 upper0039 i = powerCoefficients10 minusWeights0039 i) := by
  decide +kernel

theorem bound0039 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0039 g| ≤ (upper0039 : ℝ) :=
  abs_of_coefficients coefficients0039 upper0039 powerCoefficients10 plusWeights0039 minusWeights0039
    checked0039.1 checked0039.2.1 checked0039.2.2.1 checked0039.2.2.2
    (power_identity10 plusWeights0039) (power_identity10 minusWeights0039) g hg hmax

def envelope0039 : Envelope := ⟨coefficients0039, upper0039, bound0039⟩

def coefficients0040 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/16), (23/128), (63/256), (179/1024), (101/512), (3/16), (95/2048)]

def upper0040 : ℚ := (34048467/4096000000000)

def plusWeights0040 : Fin 11 → ℚ := ![(34048467/4096000000000), (34048467/409600000000), (306436203/819200000000), (102145401/102400000000), (717577807/409600000000), (2185293421/1024000000000), (757198607/409600000000), (116887991/102400000000), (399210379/819200000000), (267574199/2048000000000), (34048467/2048000000000)]

def minusWeights0040 : Fin 11 → ℚ := ![(34048467/4096000000000), (34048467/409600000000), (306436203/819200000000), (102145401/102400000000), (712457807/409600000000), (2104813421/1024000000000), (672837007/409600000000), (87402811/102400000000), (213662027/819200000000), (72910471/2048000000000), 0]

theorem checked0040 :
    (∀ i, 0 ≤ plusWeights0040 i) ∧
    (∀ i, 0 ≤ minusWeights0040 i) ∧
    (∀ i, plusCoefficients coefficients0040 upper0040 i = powerCoefficients10 plusWeights0040 i) ∧
    (∀ i, minusCoefficients coefficients0040 upper0040 i = powerCoefficients10 minusWeights0040 i) := by
  decide +kernel

theorem bound0040 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0040 g| ≤ (upper0040 : ℝ) :=
  abs_of_coefficients coefficients0040 upper0040 powerCoefficients10 plusWeights0040 minusWeights0040
    checked0040.1 checked0040.2.1 checked0040.2.2.1 checked0040.2.2.2
    (power_identity10 plusWeights0040) (power_identity10 minusWeights0040) g hg hmax

def envelope0040 : Envelope := ⟨coefficients0040, upper0040, bound0040⟩

def coefficients0041 : Fin 11 → ℚ := ![0, 0, 0, (1/32), (5/32), (37/128), (21/64), (447/2048), (123/1024), (27/256), (105/4096)]

def upper0041 : ℚ := (16422301/327680000000)

def plusWeights0041 : Fin 11 → ℚ := ![(16422301/327680000000), (16422301/32768000000), (147800709/65536000000), (49522903/8192000000), (352548321/32768000000), (1096281763/81920000000), (388872673/32768000000), (305173169/40960000000), (5204912573/1638400000000), (3397642097/4096000000000), (16422301/163840000000)]

def minusWeights0041 : Fin 11 → ℚ := ![(16422301/327680000000), (16422301/32768000000), (147800709/65536000000), (49010903/8192000000), (337188321/32768000000), (972928163/81920000000), (300863969/32768000000), (187495861/40960000000), (2185122877/1638400000000), (707933153/4096000000000), 0]

theorem checked0041 :
    (∀ i, 0 ≤ plusWeights0041 i) ∧
    (∀ i, 0 ≤ minusWeights0041 i) ∧
    (∀ i, plusCoefficients coefficients0041 upper0041 i = powerCoefficients10 plusWeights0041 i) ∧
    (∀ i, minusCoefficients coefficients0041 upper0041 i = powerCoefficients10 minusWeights0041 i) := by
  decide +kernel

theorem bound0041 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0041 g| ≤ (upper0041 : ℝ) :=
  abs_of_coefficients coefficients0041 upper0041 powerCoefficients10 plusWeights0041 minusWeights0041
    checked0041.1 checked0041.2.1 checked0041.2.2.1 checked0041.2.2.2
    (power_identity10 plusWeights0041) (power_identity10 minusWeights0041) g hg hmax

def envelope0041 : Envelope := ⟨coefficients0041, upper0041, bound0041⟩

def coefficients0042 : Fin 11 → ℚ := ![0, 0, 0, (1/8), (3/8), (7/16), (21/64), (89/512), (11/256), (3/128), (5/1024)]

def upper0042 : ℚ := (342468529/2048000000000)

def plusWeights0042 : Fin 11 → ℚ := ![(342468529/2048000000000), (342468529/204800000000), (3082216761/409600000000), (1033805587/51200000000), (7378719109/204800000000), (23036957327/512000000000), (8207586309/204800000000), (1292113677/51200000000), (4406564697/409600000000), (2862540949/1024000000000), (342468529/1024000000000)]

def minusWeights0042 : Fin 11 → ℚ := ![(342468529/2048000000000), (342468529/204800000000), (3082216761/409600000000), (1021005587/51200000000), (7004959109/204800000000), (20114077327/512000000000), (6176091909/204800000000), (762697497/51200000000), (70314753/16384000000), (562144341/1024000000000), 0]

theorem checked0042 :
    (∀ i, 0 ≤ plusWeights0042 i) ∧
    (∀ i, 0 ≤ minusWeights0042 i) ∧
    (∀ i, plusCoefficients coefficients0042 upper0042 i = powerCoefficients10 plusWeights0042 i) ∧
    (∀ i, minusCoefficients coefficients0042 upper0042 i = powerCoefficients10 minusWeights0042 i) := by
  decide +kernel

theorem bound0042 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0042 g| ≤ (upper0042 : ℝ) :=
  abs_of_coefficients coefficients0042 upper0042 powerCoefficients10 plusWeights0042 minusWeights0042
    checked0042.1 checked0042.2.1 checked0042.2.2.1 checked0042.2.2.2
    (power_identity10 plusWeights0042) (power_identity10 minusWeights0042) g hg hmax

def envelope0042 : Envelope := ⟨coefficients0042, upper0042, bound0042⟩

def coefficients0043 : Fin 11 → ℚ := ![0, 0, 0, 0, (-21/16), (-3/8), (-33/32), (-15/32), 0, 0, 0]

def upper0043 : ℚ := (8709/64000000)

def plusWeights0043 : Fin 11 → ℚ := ![(8709/64000000), (8709/6400000), (78381/12800000), (26127/1600000), (182049/6400000), (536007/16000000), (212703/8000000), (874413/64000000), (2631/640000), (35217/64000000), 0]

def minusWeights0043 : Fin 11 → ℚ := ![(8709/64000000), (8709/6400000), (78381/12800000), (26127/1600000), (183729/6400000), (561327/16000000), (489039/16000000), (1215747/64000000), (52071/6400000), (138963/64000000), (8709/32000000)]

theorem checked0043 :
    (∀ i, 0 ≤ plusWeights0043 i) ∧
    (∀ i, 0 ≤ minusWeights0043 i) ∧
    (∀ i, plusCoefficients coefficients0043 upper0043 i = powerCoefficients10 plusWeights0043 i) ∧
    (∀ i, minusCoefficients coefficients0043 upper0043 i = powerCoefficients10 minusWeights0043 i) := by
  decide +kernel

theorem bound0043 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0043 g| ≤ (upper0043 : ℝ) :=
  abs_of_coefficients coefficients0043 upper0043 powerCoefficients10 plusWeights0043 minusWeights0043
    checked0043.1 checked0043.2.1 checked0043.2.2.1 checked0043.2.2.2
    (power_identity10 plusWeights0043) (power_identity10 minusWeights0043) g hg hmax

def envelope0043 : Envelope := ⟨coefficients0043, upper0043, bound0043⟩

def coefficients0044 : Fin 11 → ℚ := ![0, 0, 0, 0, -1, (1/4), (-97/128), (-105/256), 0, 0, 0]

def upper0044 : ℚ := (50329/512000000)

def plusWeights0044 : Fin 11 → ℚ := ![(50329/512000000), (50329/51200000), (452961/102400000), (150987/12800000), (1051789/51200000), (3094247/128000000), (4903551/256000000), (5026707/512000000), (753607/256000000), (1607/4096000), 0]

def minusWeights0044 : Fin 11 → ℚ := ![(50329/512000000), (50329/51200000), (452961/102400000), (150987/12800000), (1062029/51200000), (3247207/128000000), (5665539/256000000), (7052253/512000000), (755599/128000000), (161141/102400000), (50329/256000000)]

theorem checked0044 :
    (∀ i, 0 ≤ plusWeights0044 i) ∧
    (∀ i, 0 ≤ minusWeights0044 i) ∧
    (∀ i, plusCoefficients coefficients0044 upper0044 i = powerCoefficients10 plusWeights0044 i) ∧
    (∀ i, minusCoefficients coefficients0044 upper0044 i = powerCoefficients10 minusWeights0044 i) := by
  decide +kernel

theorem bound0044 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0044 g| ≤ (upper0044 : ℝ) :=
  abs_of_coefficients coefficients0044 upper0044 powerCoefficients10 plusWeights0044 minusWeights0044
    checked0044.1 checked0044.2.1 checked0044.2.2.1 checked0044.2.2.2
    (power_identity10 plusWeights0044) (power_identity10 minusWeights0044) g hg hmax

def envelope0044 : Envelope := ⟨coefficients0044, upper0044, bound0044⟩

def coefficients0045 : Fin 11 → ℚ := ![0, 0, 0, 0, (-9/16), (3/8), (-83/128), (-95/256), 0, 0, 0]

def upper0045 : ℚ := (27231/512000000)

def plusWeights0045 : Fin 11 → ℚ := ![(27231/512000000), (27231/51200000), (245079/102400000), (81693/12800000), (568971/51200000), (1672833/128000000), (2647889/256000000), (2709573/512000000), (405273/256000000), (4309/20480000), 0]

def minusWeights0045 : Fin 11 → ℚ := ![(27231/512000000), (27231/51200000), (245079/102400000), (81693/12800000), (574731/51200000), (1758273/128000000), (3070621/256000000), (3825867/512000000), (410061/128000000), (87379/102400000), (27231/256000000)]

theorem checked0045 :
    (∀ i, 0 ≤ plusWeights0045 i) ∧
    (∀ i, 0 ≤ minusWeights0045 i) ∧
    (∀ i, plusCoefficients coefficients0045 upper0045 i = powerCoefficients10 plusWeights0045 i) ∧
    (∀ i, minusCoefficients coefficients0045 upper0045 i = powerCoefficients10 minusWeights0045 i) := by
  decide +kernel

theorem bound0045 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0045 g| ≤ (upper0045 : ℝ) :=
  abs_of_coefficients coefficients0045 upper0045 powerCoefficients10 plusWeights0045 minusWeights0045
    checked0045.1 checked0045.2.1 checked0045.2.2.1 checked0045.2.2.2
    (power_identity10 plusWeights0045) (power_identity10 minusWeights0045) g hg hmax

def envelope0045 : Envelope := ⟨coefficients0045, upper0045, bound0045⟩

def coefficients0046 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/2), (1/8), (-43/64), (-45/128), 0, 0, 0]

def upper0046 : ℚ := (12661/256000000)

def plusWeights0046 : Fin 11 → ℚ := ![(12661/256000000), (12661/25600000), (113949/51200000), (37983/6400000), (264601/25600000), (778523/64000000), (1234119/128000000), (1265823/256000000), (189943/128000000), (10139/51200000), 0]

def minusWeights0046 : Fin 11 → ℚ := ![(12661/256000000), (12661/25600000), (113949/51200000), (37983/6400000), (267161/25600000), (816763/64000000), (1424691/128000000), (1772817/256000000), (189901/64000000), (8101/10240000), (12661/128000000)]

theorem checked0046 :
    (∀ i, 0 ≤ plusWeights0046 i) ∧
    (∀ i, 0 ≤ minusWeights0046 i) ∧
    (∀ i, plusCoefficients coefficients0046 upper0046 i = powerCoefficients10 plusWeights0046 i) ∧
    (∀ i, minusCoefficients coefficients0046 upper0046 i = powerCoefficients10 minusWeights0046 i) := by
  decide +kernel

theorem bound0046 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0046 g| ≤ (upper0046 : ℝ) :=
  abs_of_coefficients coefficients0046 upper0046 powerCoefficients10 plusWeights0046 minusWeights0046
    checked0046.1 checked0046.2.1 checked0046.2.2.1 checked0046.2.2.2
    (power_identity10 plusWeights0046) (power_identity10 minusWeights0046) g hg hmax

def envelope0046 : Envelope := ⟨coefficients0046, upper0046, bound0046⟩

def coefficients0047 : Fin 11 → ℚ := ![0, 0, 0, 0, (-7/16), (-1/8), (-89/128), (-85/256), 0, 0, 0]

def upper0047 : ℚ := (23413/512000000)

def plusWeights0047 : Fin 11 → ℚ := ![(23413/512000000), (23413/51200000), (210717/102400000), (70239/12800000), (489433/51200000), (1441259/128000000), (2288587/256000000), (2353719/512000000), (354499/256000000), (19011/102400000), 0]

def minusWeights0047 : Fin 11 → ℚ := ![(23413/512000000), (23413/51200000), (210717/102400000), (70239/12800000), (493913/51200000), (1508779/128000000), (2628143/256000000), (3265401/512000000), (349543/128000000), (74641/102400000), (23413/256000000)]

theorem checked0047 :
    (∀ i, 0 ≤ plusWeights0047 i) ∧
    (∀ i, 0 ≤ minusWeights0047 i) ∧
    (∀ i, plusCoefficients coefficients0047 upper0047 i = powerCoefficients10 plusWeights0047 i) ∧
    (∀ i, minusCoefficients coefficients0047 upper0047 i = powerCoefficients10 minusWeights0047 i) := by
  decide +kernel

theorem bound0047 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0047 g| ≤ (upper0047 : ℝ) :=
  abs_of_coefficients coefficients0047 upper0047 powerCoefficients10 plusWeights0047 minusWeights0047
    checked0047.1 checked0047.2.1 checked0047.2.2.1 checked0047.2.2.2
    (power_identity10 plusWeights0047) (power_identity10 minusWeights0047) g hg hmax

def envelope0047 : Envelope := ⟨coefficients0047, upper0047, bound0047⟩

def coefficients0048 : Fin 11 → ℚ := ![0, 0, 0, 0, (-7/32), (-1/16), (-31/64), (-15/64), 0, 0, 0]

def upper0048 : ℚ := (589/25600000)

def plusWeights0048 : Fin 11 → ℚ := ![(589/25600000), (589/2560000), (5301/5120000), (1767/640000), (12313/2560000), (36263/6400000), (143997/32000000), (296349/128000000), (349/500000), (11993/128000000), 0]

def minusWeights0048 : Fin 11 → ℚ := ![(589/25600000), (589/2560000), (5301/5120000), (1767/640000), (497/102400), (37951/6400000), (41307/8000000), (410451/128000000), (87853/64000000), (46907/128000000), (589/12800000)]

theorem checked0048 :
    (∀ i, 0 ≤ plusWeights0048 i) ∧
    (∀ i, 0 ≤ minusWeights0048 i) ∧
    (∀ i, plusCoefficients coefficients0048 upper0048 i = powerCoefficients10 plusWeights0048 i) ∧
    (∀ i, minusCoefficients coefficients0048 upper0048 i = powerCoefficients10 minusWeights0048 i) := by
  decide +kernel

theorem bound0048 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0048 g| ≤ (upper0048 : ℝ) :=
  abs_of_coefficients coefficients0048 upper0048 powerCoefficients10 plusWeights0048 minusWeights0048
    checked0048.1 checked0048.2.1 checked0048.2.2.1 checked0048.2.2.2
    (power_identity10 plusWeights0048) (power_identity10 minusWeights0048) g hg hmax

def envelope0048 : Envelope := ⟨coefficients0048, upper0048, bound0048⟩

def coefficients0049 : Fin 11 → ℚ := ![0, 0, 0, 0, (-13/64), (5/16), (113/256), (2041/2048), 0, 0, 0]

def upper0049 : ℚ := (340919/20480000000)

def plusWeights0049 : Fin 11 → ℚ := ![(340919/20480000000), (340919/2048000000), (3068271/4096000000), (1022757/512000000), (7117699/2048000000), (20869897/5120000000), (6568203/2048000000), (33268481/20480000000), (4900859/10240000000), (1275473/20480000000), 0]

def minusWeights0049 : Fin 11 → ℚ := ![(340919/20480000000), (340919/2048000000), (3068271/4096000000), (1022757/512000000), (7200899/2048000000), (22085897/5120000000), (1550079/409600000), (48552079/20480000000), (652531/640000000), (5542907/20480000000), (340919/10240000000)]

theorem checked0049 :
    (∀ i, 0 ≤ plusWeights0049 i) ∧
    (∀ i, 0 ≤ minusWeights0049 i) ∧
    (∀ i, plusCoefficients coefficients0049 upper0049 i = powerCoefficients10 plusWeights0049 i) ∧
    (∀ i, minusCoefficients coefficients0049 upper0049 i = powerCoefficients10 minusWeights0049 i) := by
  decide +kernel

theorem bound0049 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0049 g| ≤ (upper0049 : ℝ) :=
  abs_of_coefficients coefficients0049 upper0049 powerCoefficients10 plusWeights0049 minusWeights0049
    checked0049.1 checked0049.2.1 checked0049.2.2.1 checked0049.2.2.2
    (power_identity10 plusWeights0049) (power_identity10 minusWeights0049) g hg hmax

def envelope0049 : Envelope := ⟨coefficients0049, upper0049, bound0049⟩

def coefficients0050 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/32), (39/128), (119/256), (1873/2048), 0, 0, 0]

def upper0050 : ℚ := (9793/20480000000)

def plusWeights0050 : Fin 11 → ℚ := ![(9793/20480000000), (9793/2048000000), (88137/4096000000), (29379/512000000), (199253/2048000000), (536559/5120000000), (28361/409600000), (559113/20480000000), (327/40000000), (69629/20480000000), (9793/10240000000)]

def minusWeights0050 : Fin 11 → ℚ := ![(9793/20480000000), (9793/2048000000), (88137/4096000000), (29379/512000000), (212053/2048000000), (697359/5120000000), (269501/2048000000), (1791207/20480000000), (356973/10240000000), (126231/20480000000), 0]

theorem checked0050 :
    (∀ i, 0 ≤ plusWeights0050 i) ∧
    (∀ i, 0 ≤ minusWeights0050 i) ∧
    (∀ i, plusCoefficients coefficients0050 upper0050 i = powerCoefficients10 plusWeights0050 i) ∧
    (∀ i, minusCoefficients coefficients0050 upper0050 i = powerCoefficients10 minusWeights0050 i) := by
  decide +kernel

theorem bound0050 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0050 g| ≤ (upper0050 : ℝ) :=
  abs_of_coefficients coefficients0050 upper0050 powerCoefficients10 plusWeights0050 minusWeights0050
    checked0050.1 checked0050.2.1 checked0050.2.2.1 checked0050.2.2.2
    (power_identity10 plusWeights0050) (power_identity10 minusWeights0050) g hg hmax

def envelope0050 : Envelope := ⟨coefficients0050, upper0050, bound0050⟩

def coefficients0051 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (-75/128), (-75/256), 0, 0, 0]

def upper0051 : ℚ := (63/102400000)

def plusWeights0051 : Fin 11 → ℚ := ![(63/102400000), (63/10240000), (567/20480000), (189/2560000), (1323/10240000), (3969/25600000), (1317/10240000), (7317/102400000), (1233/51200000), (381/102400000), 0]

def minusWeights0051 : Fin 11 → ℚ := ![(63/102400000), (63/10240000), (567/20480000), (189/2560000), (1323/10240000), (3969/25600000), (1329/10240000), (7803/102400000), (801/25600000), (879/102400000), (63/51200000)]

theorem checked0051 :
    (∀ i, 0 ≤ plusWeights0051 i) ∧
    (∀ i, 0 ≤ minusWeights0051 i) ∧
    (∀ i, plusCoefficients coefficients0051 upper0051 i = powerCoefficients10 plusWeights0051 i) ∧
    (∀ i, minusCoefficients coefficients0051 upper0051 i = powerCoefficients10 minusWeights0051 i) := by
  decide +kernel

theorem bound0051 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0051 g| ≤ (upper0051 : ℝ) :=
  abs_of_coefficients coefficients0051 upper0051 powerCoefficients10 plusWeights0051 minusWeights0051
    checked0051.1 checked0051.2.1 checked0051.2.2.1 checked0051.2.2.2
    (power_identity10 plusWeights0051) (power_identity10 minusWeights0051) g hg hmax

def envelope0051 : Envelope := ⟨coefficients0051, upper0051, bound0051⟩

def coefficients0052 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (25/8192), 0, 0, 0]

def upper0052 : ℚ := (1/3276800000)

def plusWeights0052 : Fin 11 → ℚ := ![(1/3276800000), (1/327680000), (9/655360000), (3/81920000), (21/327680000), (63/819200000), (21/327680000), (121/3276800000), (3/204800000), (13/3276800000), (1/1638400000)]

def minusWeights0052 : Fin 11 → ℚ := ![(1/3276800000), (1/327680000), (9/655360000), (3/81920000), (21/327680000), (63/819200000), (21/327680000), (119/3276800000), (21/1638400000), (7/3276800000), 0]

theorem checked0052 :
    (∀ i, 0 ≤ plusWeights0052 i) ∧
    (∀ i, 0 ≤ minusWeights0052 i) ∧
    (∀ i, plusCoefficients coefficients0052 upper0052 i = powerCoefficients10 plusWeights0052 i) ∧
    (∀ i, minusCoefficients coefficients0052 upper0052 i = powerCoefficients10 minusWeights0052 i) := by
  decide +kernel

theorem bound0052 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0052 g| ≤ (upper0052 : ℝ) :=
  abs_of_coefficients coefficients0052 upper0052 powerCoefficients10 plusWeights0052 minusWeights0052
    checked0052.1 checked0052.2.1 checked0052.2.2.1 checked0052.2.2.2
    (power_identity10 plusWeights0052) (power_identity10 minusWeights0052) g hg hmax

def envelope0052 : Envelope := ⟨coefficients0052, upper0052, bound0052⟩

def coefficients0053 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (25/4096), 0, 0, 0]

def upper0053 : ℚ := (1/1638400000)

def plusWeights0053 : Fin 11 → ℚ := ![(1/1638400000), (1/163840000), (9/327680000), (3/40960000), (21/163840000), (63/409600000), (21/163840000), (121/1638400000), (3/102400000), (13/1638400000), (1/819200000)]

def minusWeights0053 : Fin 11 → ℚ := ![(1/1638400000), (1/163840000), (9/327680000), (3/40960000), (21/163840000), (63/409600000), (21/163840000), (119/1638400000), (21/819200000), (7/1638400000), 0]

theorem checked0053 :
    (∀ i, 0 ≤ plusWeights0053 i) ∧
    (∀ i, 0 ≤ minusWeights0053 i) ∧
    (∀ i, plusCoefficients coefficients0053 upper0053 i = powerCoefficients10 plusWeights0053 i) ∧
    (∀ i, minusCoefficients coefficients0053 upper0053 i = powerCoefficients10 minusWeights0053 i) := by
  decide +kernel

theorem bound0053 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0053 g| ≤ (upper0053 : ℝ) :=
  abs_of_coefficients coefficients0053 upper0053 powerCoefficients10 plusWeights0053 minusWeights0053
    checked0053.1 checked0053.2.1 checked0053.2.2.1 checked0053.2.2.2
    (power_identity10 plusWeights0053) (power_identity10 minusWeights0053) g hg hmax

def envelope0053 : Envelope := ⟨coefficients0053, upper0053, bound0053⟩

def coefficients0054 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (75/8192), 0, 0, 0]

def upper0054 : ℚ := (3/3276800000)

def plusWeights0054 : Fin 11 → ℚ := ![(3/3276800000), (3/327680000), (27/655360000), (9/81920000), (63/327680000), (189/819200000), (63/327680000), (363/3276800000), (9/204800000), (39/3276800000), (3/1638400000)]

def minusWeights0054 : Fin 11 → ℚ := ![(3/3276800000), (3/327680000), (27/655360000), (9/81920000), (63/327680000), (189/819200000), (63/327680000), (357/3276800000), (63/1638400000), (21/3276800000), 0]

theorem checked0054 :
    (∀ i, 0 ≤ plusWeights0054 i) ∧
    (∀ i, 0 ≤ minusWeights0054 i) ∧
    (∀ i, plusCoefficients coefficients0054 upper0054 i = powerCoefficients10 plusWeights0054 i) ∧
    (∀ i, minusCoefficients coefficients0054 upper0054 i = powerCoefficients10 minusWeights0054 i) := by
  decide +kernel

theorem bound0054 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0054 g| ≤ (upper0054 : ℝ) :=
  abs_of_coefficients coefficients0054 upper0054 powerCoefficients10 plusWeights0054 minusWeights0054
    checked0054.1 checked0054.2.1 checked0054.2.2.1 checked0054.2.2.2
    (power_identity10 plusWeights0054) (power_identity10 minusWeights0054) g hg hmax

def envelope0054 : Envelope := ⟨coefficients0054, upper0054, bound0054⟩

def coefficients0055 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (75/4096), 0, 0, 0]

def upper0055 : ℚ := (3/1638400000)

def plusWeights0055 : Fin 11 → ℚ := ![(3/1638400000), (3/163840000), (27/327680000), (9/40960000), (63/163840000), (189/409600000), (63/163840000), (363/1638400000), (9/102400000), (39/1638400000), (3/819200000)]

def minusWeights0055 : Fin 11 → ℚ := ![(3/1638400000), (3/163840000), (27/327680000), (9/40960000), (63/163840000), (189/409600000), (63/163840000), (357/1638400000), (63/819200000), (21/1638400000), 0]

theorem checked0055 :
    (∀ i, 0 ≤ plusWeights0055 i) ∧
    (∀ i, 0 ≤ minusWeights0055 i) ∧
    (∀ i, plusCoefficients coefficients0055 upper0055 i = powerCoefficients10 plusWeights0055 i) ∧
    (∀ i, minusCoefficients coefficients0055 upper0055 i = powerCoefficients10 minusWeights0055 i) := by
  decide +kernel

theorem bound0055 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0055 g| ≤ (upper0055 : ℝ) :=
  abs_of_coefficients coefficients0055 upper0055 powerCoefficients10 plusWeights0055 minusWeights0055
    checked0055.1 checked0055.2.1 checked0055.2.2.1 checked0055.2.2.2
    (power_identity10 plusWeights0055) (power_identity10 minusWeights0055) g hg hmax

def envelope0055 : Envelope := ⟨coefficients0055, upper0055, bound0055⟩

def coefficients0056 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (225/8192), 0, 0, 0]

def upper0056 : ℚ := (9/3276800000)

def plusWeights0056 : Fin 11 → ℚ := ![(9/3276800000), (9/327680000), (81/655360000), (27/81920000), (189/327680000), (567/819200000), (189/327680000), (1089/3276800000), (27/204800000), (117/3276800000), (9/1638400000)]

def minusWeights0056 : Fin 11 → ℚ := ![(9/3276800000), (9/327680000), (81/655360000), (27/81920000), (189/327680000), (567/819200000), (189/327680000), (1071/3276800000), (189/1638400000), (63/3276800000), 0]

theorem checked0056 :
    (∀ i, 0 ≤ plusWeights0056 i) ∧
    (∀ i, 0 ≤ minusWeights0056 i) ∧
    (∀ i, plusCoefficients coefficients0056 upper0056 i = powerCoefficients10 plusWeights0056 i) ∧
    (∀ i, minusCoefficients coefficients0056 upper0056 i = powerCoefficients10 minusWeights0056 i) := by
  decide +kernel

theorem bound0056 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0056 g| ≤ (upper0056 : ℝ) :=
  abs_of_coefficients coefficients0056 upper0056 powerCoefficients10 plusWeights0056 minusWeights0056
    checked0056.1 checked0056.2.1 checked0056.2.2.1 checked0056.2.2.2
    (power_identity10 plusWeights0056) (power_identity10 minusWeights0056) g hg hmax

def envelope0056 : Envelope := ⟨coefficients0056, upper0056, bound0056⟩

def coefficients0057 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (225/4096), 0, 0, 0]

def upper0057 : ℚ := (9/1638400000)

def plusWeights0057 : Fin 11 → ℚ := ![(9/1638400000), (9/163840000), (81/327680000), (27/40960000), (189/163840000), (567/409600000), (189/163840000), (1089/1638400000), (27/102400000), (117/1638400000), (9/819200000)]

def minusWeights0057 : Fin 11 → ℚ := ![(9/1638400000), (9/163840000), (81/327680000), (27/40960000), (189/163840000), (567/409600000), (189/163840000), (1071/1638400000), (189/819200000), (63/1638400000), 0]

theorem checked0057 :
    (∀ i, 0 ≤ plusWeights0057 i) ∧
    (∀ i, 0 ≤ minusWeights0057 i) ∧
    (∀ i, plusCoefficients coefficients0057 upper0057 i = powerCoefficients10 plusWeights0057 i) ∧
    (∀ i, minusCoefficients coefficients0057 upper0057 i = powerCoefficients10 minusWeights0057 i) := by
  decide +kernel

theorem bound0057 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0057 g| ≤ (upper0057 : ℝ) :=
  abs_of_coefficients coefficients0057 upper0057 powerCoefficients10 plusWeights0057 minusWeights0057
    checked0057.1 checked0057.2.1 checked0057.2.2.1 checked0057.2.2.2
    (power_identity10 plusWeights0057) (power_identity10 minusWeights0057) g hg hmax

def envelope0057 : Envelope := ⟨coefficients0057, upper0057, bound0057⟩

def coefficients0058 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (225/2048), 0, 0, 0]

def upper0058 : ℚ := (9/819200000)

def plusWeights0058 : Fin 11 → ℚ := ![(9/819200000), (9/81920000), (81/163840000), (27/20480000), (189/81920000), (567/204800000), (189/81920000), (1089/819200000), (27/51200000), (117/819200000), (9/409600000)]

def minusWeights0058 : Fin 11 → ℚ := ![(9/819200000), (9/81920000), (81/163840000), (27/20480000), (189/81920000), (567/204800000), (189/81920000), (1071/819200000), (189/409600000), (63/819200000), 0]

theorem checked0058 :
    (∀ i, 0 ≤ plusWeights0058 i) ∧
    (∀ i, 0 ≤ minusWeights0058 i) ∧
    (∀ i, plusCoefficients coefficients0058 upper0058 i = powerCoefficients10 plusWeights0058 i) ∧
    (∀ i, minusCoefficients coefficients0058 upper0058 i = powerCoefficients10 minusWeights0058 i) := by
  decide +kernel

theorem bound0058 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0058 g| ≤ (upper0058 : ℝ) :=
  abs_of_coefficients coefficients0058 upper0058 powerCoefficients10 plusWeights0058 minusWeights0058
    checked0058.1 checked0058.2.1 checked0058.2.2.1 checked0058.2.2.2
    (power_identity10 plusWeights0058) (power_identity10 minusWeights0058) g hg hmax

def envelope0058 : Envelope := ⟨coefficients0058, upper0058, bound0058⟩

def coefficients0059 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (35/128), (45/256), (1315/2048), 0, 0, 0]

def upper0059 : ℚ := (12183/4096000000)

def plusWeights0059 : Fin 11 → ℚ := ![(12183/4096000000), (12183/409600000), (109647/819200000), (36549/102400000), (255843/409600000), (770329/1024000000), (52303/81920000), (1577103/4096000000), (2599/16000000), (181499/4096000000), (12183/2048000000)]

def minusWeights0059 : Fin 11 → ℚ := ![(12183/4096000000), (12183/409600000), (109647/819200000), (36549/102400000), (255843/409600000), (764729/1024000000), (250171/409600000), (1346817/4096000000), (215563/2048000000), (62161/4096000000), 0]

theorem checked0059 :
    (∀ i, 0 ≤ plusWeights0059 i) ∧
    (∀ i, 0 ≤ minusWeights0059 i) ∧
    (∀ i, plusCoefficients coefficients0059 upper0059 i = powerCoefficients10 plusWeights0059 i) ∧
    (∀ i, minusCoefficients coefficients0059 upper0059 i = powerCoefficients10 minusWeights0059 i) := by
  decide +kernel

theorem bound0059 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0059 g| ≤ (upper0059 : ℝ) :=
  abs_of_coefficients coefficients0059 upper0059 powerCoefficients10 plusWeights0059 minusWeights0059
    checked0059.1 checked0059.2.1 checked0059.2.2.1 checked0059.2.2.2
    (power_identity10 plusWeights0059) (power_identity10 minusWeights0059) g hg hmax

def envelope0059 : Envelope := ⟨coefficients0059, upper0059, bound0059⟩

def coefficients0060 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (35/64), (45/128), (1405/2048), 0, 0, 0]

def upper0060 : ℚ := (24121/4096000000)

def plusWeights0060 : Fin 11 → ℚ := ![(24121/4096000000), (24121/409600000), (217089/819200000), (72363/102400000), (506541/409600000), (1525223/1024000000), (103577/81920000), (3124561/4096000000), (82433/256000000), (359813/4096000000), (24121/2048000000)]

def minusWeights0060 : Fin 11 → ℚ := ![(24121/4096000000), (24121/409600000), (217089/819200000), (72363/102400000), (506541/409600000), (1514023/1024000000), (495197/409600000), (2664479/4096000000), (425981/2048000000), (122607/4096000000), 0]

theorem checked0060 :
    (∀ i, 0 ≤ plusWeights0060 i) ∧
    (∀ i, 0 ≤ minusWeights0060 i) ∧
    (∀ i, plusCoefficients coefficients0060 upper0060 i = powerCoefficients10 plusWeights0060 i) ∧
    (∀ i, minusCoefficients coefficients0060 upper0060 i = powerCoefficients10 minusWeights0060 i) := by
  decide +kernel

theorem bound0060 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0060 g| ≤ (upper0060 : ℝ) :=
  abs_of_coefficients coefficients0060 upper0060 powerCoefficients10 plusWeights0060 minusWeights0060
    checked0060.1 checked0060.2.1 checked0060.2.2.1 checked0060.2.2.2
    (power_identity10 plusWeights0060) (power_identity10 minusWeights0060) g hg hmax

def envelope0060 : Envelope := ⟨coefficients0060, upper0060, bound0060⟩

def coefficients0061 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/32), (3/16), (41/256), (67/128), 0, 0, 0]

def upper0061 : ℚ := (917/80000000)

def plusWeights0061 : Fin 11 → ℚ := ![(917/80000000), (917/8000000), (8253/16000000), (2751/2000000), (4833/2000000), (117867/40000000), (130933/51200000), (2025527/1280000000), (865671/1280000000), (231741/1280000000), (917/40000000)]

def minusWeights0061 : Fin 11 → ℚ := ![(917/80000000), (917/8000000), (8253/16000000), (2751/2000000), (9591/4000000), (113217/40000000), (577783/256000000), (1495753/1280000000), (454809/1280000000), (61699/1280000000), 0]

theorem checked0061 :
    (∀ i, 0 ≤ plusWeights0061 i) ∧
    (∀ i, 0 ≤ minusWeights0061 i) ∧
    (∀ i, plusCoefficients coefficients0061 upper0061 i = powerCoefficients10 plusWeights0061 i) ∧
    (∀ i, minusCoefficients coefficients0061 upper0061 i = powerCoefficients10 minusWeights0061 i) := by
  decide +kernel

theorem bound0061 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0061 g| ≤ (upper0061 : ℝ) :=
  abs_of_coefficients coefficients0061 upper0061 powerCoefficients10 plusWeights0061 minusWeights0061
    checked0061.1 checked0061.2.1 checked0061.2.2.1 checked0061.2.2.2
    (power_identity10 plusWeights0061) (power_identity10 minusWeights0061) g hg hmax

def envelope0061 : Envelope := ⟨coefficients0061, upper0061, bound0061⟩

def coefficients0062 : Fin 11 → ℚ := ![0, 0, 0, 0, (9/32), (9/128), (21/128), (93/256), 0, 0, 0]

def upper0062 : ℚ := (74313/2560000000)

def plusWeights0062 : Fin 11 → ℚ := ![(74313/2560000000), (74313/256000000), (668817/512000000), (222939/64000000), (1567773/256000000), (4790169/640000000), (333903/51200000), (10377333/2560000000), (1111221/640000000), (1186089/2560000000), (74313/1280000000)]

def minusWeights0062 : Fin 11 → ℚ := ![(74313/2560000000), (74313/256000000), (668817/512000000), (222939/64000000), (1553373/256000000), (4573269/640000000), (1451631/256000000), (7457787/2560000000), (1121643/1280000000), (300171/2560000000), 0]

theorem checked0062 :
    (∀ i, 0 ≤ plusWeights0062 i) ∧
    (∀ i, 0 ≤ minusWeights0062 i) ∧
    (∀ i, plusCoefficients coefficients0062 upper0062 i = powerCoefficients10 plusWeights0062 i) ∧
    (∀ i, minusCoefficients coefficients0062 upper0062 i = powerCoefficients10 minusWeights0062 i) := by
  decide +kernel

theorem bound0062 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0062 g| ≤ (upper0062 : ℝ) :=
  abs_of_coefficients coefficients0062 upper0062 powerCoefficients10 plusWeights0062 minusWeights0062
    checked0062.1 checked0062.2.1 checked0062.2.2.1 checked0062.2.2.2
    (power_identity10 plusWeights0062) (power_identity10 minusWeights0062) g hg hmax

def envelope0062 : Envelope := ⟨coefficients0062, upper0062, bound0062⟩

def coefficients0063 : Fin 11 → ℚ := ![0, 0, 0, 0, (9/16), (-13/32), (-3/128), (83/2048), 0, 0, 0]

def upper0063 : ℚ := (1068403/20480000000)

def plusWeights0063 : Fin 11 → ℚ := ![(1068403/20480000000), (1068403/2048000000), (9615627/4096000000), (3205209/512000000), (22551663/2048000000), (69016589/5120000000), (4824563/409600000), (150414523/20480000000), (4032719/1280000000), (17178359/20480000000), (1068403/10240000000)]

def minusWeights0063 : Fin 11 → ℚ := ![(1068403/20480000000), (1068403/2048000000), (9615627/4096000000), (3205209/512000000), (22321263/2048000000), (65602189/5120000000), (20750111/2048000000), (106002197/20480000000), (15816383/10240000000), (4189701/20480000000), 0]

theorem checked0063 :
    (∀ i, 0 ≤ plusWeights0063 i) ∧
    (∀ i, 0 ≤ minusWeights0063 i) ∧
    (∀ i, plusCoefficients coefficients0063 upper0063 i = powerCoefficients10 plusWeights0063 i) ∧
    (∀ i, minusCoefficients coefficients0063 upper0063 i = powerCoefficients10 minusWeights0063 i) := by
  decide +kernel

theorem bound0063 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0063 g| ≤ (upper0063 : ℝ) :=
  abs_of_coefficients coefficients0063 upper0063 powerCoefficients10 plusWeights0063 minusWeights0063
    checked0063.1 checked0063.2.1 checked0063.2.2.1 checked0063.2.2.2
    (power_identity10 plusWeights0063) (power_identity10 minusWeights0063) g hg hmax

def envelope0063 : Envelope := ⟨coefficients0063, upper0063, bound0063⟩

end BilayerDressed.CubicQuarticEnvelopes

import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0096 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/64), (-43/512), (-763/4096), (-235/2048), (-463/2048), (-1589/16384)]

def upper0096 : ℚ := (93838629/163840000000000)

def plusWeights0096 : Fin 11 → ℚ := ![(93838629/163840000000000), (93838629/16384000000000), (844547661/32768000000000), (281515887/4096000000000), (1970611209/16384000000000), (5892633627/40960000000000), (1930835209/16384000000000), (260863587/4096000000000), (672566861/32768000000000), (1959109/655360000000), 0]

def minusWeights0096 : Fin 11 → ℚ := ![(93838629/163840000000000), (93838629/16384000000000), (844547661/32768000000000), (281515887/4096000000000), (1970611209/16384000000000), (5931033627/40960000000000), (2010387209/16384000000000), (302168187/4096000000000), (1016528461/32768000000000), (138699533/16384000000000), (93838629/81920000000000)]

theorem checked0096 :
    (∀ i, 0 ≤ plusWeights0096 i) ∧
    (∀ i, 0 ≤ minusWeights0096 i) ∧
    (∀ i, plusCoefficients coefficients0096 upper0096 i = powerCoefficients10 plusWeights0096 i) ∧
    (∀ i, minusCoefficients coefficients0096 upper0096 i = powerCoefficients10 minusWeights0096 i) := by
  decide +kernel

theorem bound0096 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0096 g| ≤ (upper0096 : ℝ) :=
  abs_of_coefficients coefficients0096 upper0096 powerCoefficients10 plusWeights0096 minusWeights0096
    checked0096.1 checked0096.2.1 checked0096.2.2.1 checked0096.2.2.2
    (power_identity10 plusWeights0096) (power_identity10 minusWeights0096) g hg hmax

def envelope0096 : Envelope := ⟨coefficients0096, upper0096, bound0096⟩

def coefficients0097 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/64), (-43/512), (-1191/8192), (-415/4096), (-2549/16384), (-1039/16384)]

def upper0097 : ℚ := (93134529/163840000000000)

def plusWeights0097 : Fin 11 → ℚ := ![(93134529/163840000000000), (93134529/16384000000000), (838210761/32768000000000), (279403587/4096000000000), (1955825109/16384000000000), (5848275327/40960000000000), (1916049109/16384000000000), (258768037/4096000000000), (666636361/32768000000000), (2424009/819200000000), 0]

def minusWeights0097 : Fin 11 → ℚ := ![(93134529/163840000000000), (93134529/16384000000000), (838210761/32768000000000), (279403587/4096000000000), (1955825109/16384000000000), (5886675327/40960000000000), (1995601109/16384000000000), (300039137/4096000000000), (1009785161/32768000000000), (68894439/8192000000000), (93134529/81920000000000)]

theorem checked0097 :
    (∀ i, 0 ≤ plusWeights0097 i) ∧
    (∀ i, 0 ≤ minusWeights0097 i) ∧
    (∀ i, plusCoefficients coefficients0097 upper0097 i = powerCoefficients10 plusWeights0097 i) ∧
    (∀ i, minusCoefficients coefficients0097 upper0097 i = powerCoefficients10 minusWeights0097 i) := by
  decide +kernel

theorem bound0097 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0097 g| ≤ (upper0097 : ℝ) :=
  abs_of_coefficients coefficients0097 upper0097 powerCoefficients10 plusWeights0097 minusWeights0097
    checked0097.1 checked0097.2.1 checked0097.2.2.1 checked0097.2.2.2
    (power_identity10 plusWeights0097) (power_identity10 minusWeights0097) g hg hmax

def envelope0097 : Envelope := ⟨coefficients0097, upper0097, bound0097⟩

def coefficients0098 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-23/512), (-31/1024), (-379/4096), (-39/512), (-1209/16384), (-873/32768)]

def upper0098 : ℚ := (160426653/327680000000000)

def plusWeights0098 : Fin 11 → ℚ := ![(160426653/327680000000000), (160426653/32768000000000), (1443839877/65536000000000), (481279959/8192000000000), (3368959713/32768000000000), (10070079139/81920000000000), (3294367713/32768000000000), (443412159/8192000000000), (1135666757/65536000000000), (16379343/6553600000000), 0]

def minusWeights0098 : Fin 11 → ℚ := ![(160426653/327680000000000), (160426653/32768000000000), (1443839877/65536000000000), (481279959/8192000000000), (3368959713/32768000000000), (10143679139/81920000000000), (3443551713/32768000000000), (519147759/8192000000000), (1752012997/65536000000000), (238956591/32768000000000), (160426653/163840000000000)]

theorem checked0098 :
    (∀ i, 0 ≤ plusWeights0098 i) ∧
    (∀ i, 0 ≤ minusWeights0098 i) ∧
    (∀ i, plusCoefficients coefficients0098 upper0098 i = powerCoefficients10 plusWeights0098 i) ∧
    (∀ i, minusCoefficients coefficients0098 upper0098 i = powerCoefficients10 minusWeights0098 i) := by
  decide +kernel

theorem bound0098 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0098 g| ≤ (upper0098 : ℝ) :=
  abs_of_coefficients coefficients0098 upper0098 powerCoefficients10 plusWeights0098 minusWeights0098
    checked0098.1 checked0098.2.1 checked0098.2.2.1 checked0098.2.2.2
    (power_identity10 plusWeights0098) (power_identity10 minusWeights0098) g hg hmax

def envelope0098 : Envelope := ⟨coefficients0098, upper0098, bound0098⟩

def coefficients0099 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-23/512), (-31/1024), (-503/8192), (-111/2048), (-619/16384), (-373/32768)]

def upper0099 : ℚ := (159322353/327680000000000)

def plusWeights0099 : Fin 11 → ℚ := ![(159322353/327680000000000), (159322353/32768000000000), (1433901177/65536000000000), (477967059/8192000000000), (3345769413/32768000000000), (10000508239/81920000000000), (3271177413/32768000000000), (440124759/8192000000000), (1126354457/65536000000000), (16222799/6553600000000), 0]

def minusWeights0099 : Fin 11 → ℚ := ![(159322353/327680000000000), (159322353/32768000000000), (1433901177/65536000000000), (477967059/8192000000000), (3345769413/32768000000000), (10074108239/81920000000000), (3420361413/32768000000000), (515809359/8192000000000), (1741447897/65536000000000), (237530711/32768000000000), (159322353/163840000000000)]

theorem checked0099 :
    (∀ i, 0 ≤ plusWeights0099 i) ∧
    (∀ i, 0 ≤ minusWeights0099 i) ∧
    (∀ i, plusCoefficients coefficients0099 upper0099 i = powerCoefficients10 plusWeights0099 i) ∧
    (∀ i, minusCoefficients coefficients0099 upper0099 i = powerCoefficients10 minusWeights0099 i) := by
  decide +kernel

theorem bound0099 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0099 g| ≤ (upper0099 : ℝ) :=
  abs_of_coefficients coefficients0099 upper0099 powerCoefficients10 plusWeights0099 minusWeights0099
    checked0099.1 checked0099.2.1 checked0099.2.2.1 checked0099.2.2.2
    (power_identity10 plusWeights0099) (power_identity10 minusWeights0099) g hg hmax

def envelope0099 : Envelope := ⟨coefficients0099, upper0099, bound0099⟩

def coefficients0100 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-21/512), (-33/1024), (-321/4096), (-27/512), (-165/4096), (-225/16384)]

def upper0100 : ℚ := (2954289/6553600000000)

def plusWeights0100 : Fin 11 → ℚ := ![(2954289/6553600000000), (2954289/655360000000), (26588601/1310720000000), (8862867/163840000000), (62040069/655360000000), (185448207/1638400000000), (60674949/655360000000), (8168463/163840000000), (104638269/6553600000000), (7548417/3276800000000), 0]

def minusWeights0100 : Fin 11 → ℚ := ![(2954289/6553600000000), (2954289/655360000000), (26588601/1310720000000), (8862867/163840000000), (62040069/655360000000), (186792207/1638400000000), (63405189/655360000000), (9557271/163840000000), (161247741/6553600000000), (21994473/3276800000000), (2954289/3276800000000)]

theorem checked0100 :
    (∀ i, 0 ≤ plusWeights0100 i) ∧
    (∀ i, 0 ≤ minusWeights0100 i) ∧
    (∀ i, plusCoefficients coefficients0100 upper0100 i = powerCoefficients10 plusWeights0100 i) ∧
    (∀ i, minusCoefficients coefficients0100 upper0100 i = powerCoefficients10 minusWeights0100 i) := by
  decide +kernel

theorem bound0100 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0100 g| ≤ (upper0100 : ℝ) :=
  abs_of_coefficients coefficients0100 upper0100 powerCoefficients10 plusWeights0100 minusWeights0100
    checked0100.1 checked0100.2.1 checked0100.2.2.1 checked0100.2.2.2
    (power_identity10 plusWeights0100) (power_identity10 minusWeights0100) g hg hmax

def envelope0100 : Envelope := ⟨coefficients0100, upper0100, bound0100⟩

def coefficients0101 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-21/512), (-33/1024), (-437/8192), (-151/4096), (-615/32768), (-325/65536)]

def upper0101 : ℚ := (11746809/26214400000000)

def plusWeights0101 : Fin 11 → ℚ := ![(11746809/26214400000000), (11746809/2621440000000), (105721281/5242880000000), (35240427/655360000000), (246682989/2621440000000), (737360967/6553600000000), (241222509/2621440000000), (32464451/655360000000), (415588421/26214400000000), (1197791/524288000000), 0]

def minusWeights0101 : Fin 11 → ℚ := ![(11746809/26214400000000), (11746809/2621440000000), (105721281/5242880000000), (35240427/655360000000), (246682989/2621440000000), (742736967/6553600000000), (252143469/2621440000000), (38016403/655360000000), (641624389/26214400000000), (17504663/2621440000000), (11746809/13107200000000)]

theorem checked0101 :
    (∀ i, 0 ≤ plusWeights0101 i) ∧
    (∀ i, 0 ≤ minusWeights0101 i) ∧
    (∀ i, plusCoefficients coefficients0101 upper0101 i = powerCoefficients10 plusWeights0101 i) ∧
    (∀ i, minusCoefficients coefficients0101 upper0101 i = powerCoefficients10 minusWeights0101 i) := by
  decide +kernel

theorem bound0101 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0101 g| ≤ (upper0101 : ℝ) :=
  abs_of_coefficients coefficients0101 upper0101 powerCoefficients10 plusWeights0101 minusWeights0101
    checked0101.1 checked0101.2.1 checked0101.2.2.1 checked0101.2.2.2
    (power_identity10 plusWeights0101) (power_identity10 minusWeights0101) g hg hmax

def envelope0101 : Envelope := ⟨coefficients0101, upper0101, bound0101⟩

def coefficients0102 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (3/256), (-251/2048), (-295/2048), (-3911/32768), (-2667/65536)]

def upper0102 : ℚ := (206176887/655360000000000)

def plusWeights0102 : Fin 11 → ℚ := ![(206176887/655360000000000), (206176887/65536000000000), (1855591983/131072000000000), (618530661/16384000000000), (4329714627/65536000000000), (12937943881/163840000000000), (4228082627/65536000000000), (567897861/16384000000000), (1450199983/131072000000000), (20848533/13107200000000), 0]

def minusWeights0102 : Fin 11 → ℚ := ![(206176887/655360000000000), (206176887/65536000000000), (1855591983/131072000000000), (618530661/16384000000000), (4329714627/65536000000000), (13040343881/163840000000000), (4431346627/65536000000000), (669163461/16384000000000), (2260983983/131072000000000), (308111109/65536000000000), (206176887/327680000000000)]

theorem checked0102 :
    (∀ i, 0 ≤ plusWeights0102 i) ∧
    (∀ i, 0 ≤ minusWeights0102 i) ∧
    (∀ i, plusCoefficients coefficients0102 upper0102 i = powerCoefficients10 plusWeights0102 i) ∧
    (∀ i, minusCoefficients coefficients0102 upper0102 i = powerCoefficients10 minusWeights0102 i) := by
  decide +kernel

theorem bound0102 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0102 g| ≤ (upper0102 : ℝ) :=
  abs_of_coefficients coefficients0102 upper0102 powerCoefficients10 plusWeights0102 minusWeights0102
    checked0102.1 checked0102.2.1 checked0102.2.2.1 checked0102.2.2.2
    (power_identity10 plusWeights0102) (power_identity10 minusWeights0102) g hg hmax

def envelope0102 : Envelope := ⟨coefficients0102, upper0102, bound0102⟩

def coefficients0103 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (7/512), (143/8192), (2659/32768), (2323/65536), (8515/524288)]

def upper0103 : ℚ := (310623849/1048576000000000)

def plusWeights0103 : Fin 11 → ℚ := ![(310623849/1048576000000000), (310623849/104857600000000), (2795614641/209715200000000), (931871547/26214400000000), (6523100829/104857600000000), (19487382487/262144000000000), (6360694429/104857600000000), (851430907/26214400000000), (2158726257/209715200000000), (766206309/524288000000000), 0]

def minusWeights0103 : Fin 11 → ℚ := ![(310623849/1048576000000000), (310623849/104857600000000), (2795614641/209715200000000), (931871547/26214400000000), (6523100829/104857600000000), (19651222487/262144000000000), (6685507229/104857600000000), (1012312187/26214400000000), (137300121/8388608000000), (2340032181/524288000000000), (310623849/524288000000000)]

theorem checked0103 :
    (∀ i, 0 ≤ plusWeights0103 i) ∧
    (∀ i, 0 ≤ minusWeights0103 i) ∧
    (∀ i, plusCoefficients coefficients0103 upper0103 i = powerCoefficients10 plusWeights0103 i) ∧
    (∀ i, minusCoefficients coefficients0103 upper0103 i = powerCoefficients10 minusWeights0103 i) := by
  decide +kernel

theorem bound0103 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0103 g| ≤ (upper0103 : ℝ) :=
  abs_of_coefficients coefficients0103 upper0103 powerCoefficients10 plusWeights0103 minusWeights0103
    checked0103.1 checked0103.2.1 checked0103.2.2.1 checked0103.2.2.2
    (power_identity10 plusWeights0103) (power_identity10 minusWeights0103) g hg hmax

def envelope0103 : Envelope := ⟨coefficients0103, upper0103, bound0103⟩

def coefficients0104 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (7/512), (143/8192), (3199/32768), (3103/65536), (18475/524288)]

def upper0104 : ℚ := (310436577/1048576000000000)

def plusWeights0104 : Fin 11 → ℚ := ![(310436577/1048576000000000), (310436577/104857600000000), (2793929193/209715200000000), (931309731/26214400000000), (6519168117/104857600000000), (19475584351/262144000000000), (6356761717/104857600000000), (850869091/26214400000000), (2157075369/209715200000000), (765448989/524288000000000), 0]

def minusWeights0104 : Fin 11 → ℚ := ![(310436577/1048576000000000), (310436577/104857600000000), (2793929193/209715200000000), (931309731/26214400000000), (6519168117/104857600000000), (19639424351/262144000000000), (6681574517/104857600000000), (1011750371/26214400000000), (3430783017/209715200000000), (2338916781/524288000000000), (310436577/524288000000000)]

theorem checked0104 :
    (∀ i, 0 ≤ plusWeights0104 i) ∧
    (∀ i, 0 ≤ minusWeights0104 i) ∧
    (∀ i, plusCoefficients coefficients0104 upper0104 i = powerCoefficients10 plusWeights0104 i) ∧
    (∀ i, minusCoefficients coefficients0104 upper0104 i = powerCoefficients10 minusWeights0104 i) := by
  decide +kernel

theorem bound0104 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0104 g| ≤ (upper0104 : ℝ) :=
  abs_of_coefficients coefficients0104 upper0104 powerCoefficients10 plusWeights0104 minusWeights0104
    checked0104.1 checked0104.2.1 checked0104.2.2.1 checked0104.2.2.2
    (power_identity10 plusWeights0104) (power_identity10 minusWeights0104) g hg hmax

def envelope0104 : Envelope := ⟨coefficients0104, upper0104, bound0104⟩

def coefficients0105 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (41/1024), (91/4096), (3371/16384), (3647/32768), (33845/262144)]

def upper0105 : ℚ := (140539359/524288000000000)

def plusWeights0105 : Fin 11 → ℚ := ![(140539359/524288000000000), (140539359/52428800000000), (1264854231/104857600000000), (421618077/13107200000000), (2951326539/52428800000000), (8813019617/131072000000000), (2871505739/52428800000000), (382786397/13107200000000), (192655851/20971520000000), (337935891/262144000000000), 0]

def minusWeights0105 : Fin 11 → ℚ := ![(140539359/524288000000000), (140539359/52428800000000), (1264854231/104857600000000), (421618077/13107200000000), (2951326539/52428800000000), (8894939617/131072000000000), (3031147339/52428800000000), (460449757/13107200000000), (1566429207/104857600000000), (1067457699/262144000000000), (140539359/262144000000000)]

theorem checked0105 :
    (∀ i, 0 ≤ plusWeights0105 i) ∧
    (∀ i, 0 ≤ minusWeights0105 i) ∧
    (∀ i, plusCoefficients coefficients0105 upper0105 i = powerCoefficients10 plusWeights0105 i) ∧
    (∀ i, minusCoefficients coefficients0105 upper0105 i = powerCoefficients10 minusWeights0105 i) := by
  decide +kernel

theorem bound0105 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0105 g| ≤ (upper0105 : ℝ) :=
  abs_of_coefficients coefficients0105 upper0105 powerCoefficients10 plusWeights0105 minusWeights0105
    checked0105.1 checked0105.2.1 checked0105.2.2.1 checked0105.2.2.2
    (power_identity10 plusWeights0105) (power_identity10 minusWeights0105) g hg hmax

def envelope0105 : Envelope := ⟨coefficients0105, upper0105, bound0105⟩

def coefficients0106 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (21/512), (-325/2048), (-411/2048), (-6269/32768), (-4513/65536)]

def upper0106 : ℚ := (189765093/655360000000000)

def plusWeights0106 : Fin 11 → ℚ := ![(189765093/655360000000000), (189765093/65536000000000), (1707885837/131072000000000), (569295279/16384000000000), (3985066953/65536000000000), (11904000859/163840000000000), (3885354953/65536000000000), (520523279/16384000000000), (1324038797/131072000000000), (18944303/13107200000000), 0]

def minusWeights0106 : Fin 11 → ℚ := ![(189765093/655360000000000), (189765093/65536000000000), (1707885837/131072000000000), (569295279/16384000000000), (3985066953/65536000000000), (12006400859/163840000000000), (4084778953/65536000000000), (618067279/16384000000000), (2091732877/131072000000000), (284808671/65536000000000), (189765093/327680000000000)]

theorem checked0106 :
    (∀ i, 0 ≤ plusWeights0106 i) ∧
    (∀ i, 0 ≤ minusWeights0106 i) ∧
    (∀ i, plusCoefficients coefficients0106 upper0106 i = powerCoefficients10 plusWeights0106 i) ∧
    (∀ i, minusCoefficients coefficients0106 upper0106 i = powerCoefficients10 minusWeights0106 i) := by
  decide +kernel

theorem bound0106 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0106 g| ≤ (upper0106 : ℝ) :=
  abs_of_coefficients coefficients0106 upper0106 powerCoefficients10 plusWeights0106 minusWeights0106
    checked0106.1 checked0106.2.1 checked0106.2.2.1 checked0106.2.2.2
    (power_identity10 plusWeights0106) (power_identity10 minusWeights0106) g hg hmax

def envelope0106 : Envelope := ⟨coefficients0106, upper0106, bound0106⟩

def coefficients0107 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (17/256), (-1/2048), (2345/8192), (2625/16384), (11245/65536)]

def upper0107 : ℚ := (31863951/131072000000000)

def plusWeights0107 : Fin 11 → ℚ := ![(31863951/131072000000000), (31863951/13107200000000), (286775559/26214400000000), (95591853/3276800000000), (669142971/13107200000000), (1997188913/32768000000000), (649533371/13107200000000), (86222093/3276800000000), (215371559/26214400000000), (14940771/13107200000000), 0]

def minusWeights0107 : Fin 11 → ℚ := ![(31863951/131072000000000), (31863951/13107200000000), (286775559/26214400000000), (95591853/3276800000000), (669142971/13107200000000), (2017668913/32768000000000), (688752571/13107200000000), (104961613/3276800000000), (358179559/26214400000000), (48787131/13107200000000), (31863951/65536000000000)]

theorem checked0107 :
    (∀ i, 0 ≤ plusWeights0107 i) ∧
    (∀ i, 0 ≤ minusWeights0107 i) ∧
    (∀ i, plusCoefficients coefficients0107 upper0107 i = powerCoefficients10 plusWeights0107 i) ∧
    (∀ i, minusCoefficients coefficients0107 upper0107 i = powerCoefficients10 minusWeights0107 i) := by
  decide +kernel

theorem bound0107 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0107 g| ≤ (upper0107 : ℝ) :=
  abs_of_coefficients coefficients0107 upper0107 powerCoefficients10 plusWeights0107 minusWeights0107
    checked0107.1 checked0107.2.1 checked0107.2.2.1 checked0107.2.2.2
    (power_identity10 plusWeights0107) (power_identity10 minusWeights0107) g hg hmax

def envelope0107 : Envelope := ⟨coefficients0107, upper0107, bound0107⟩

def coefficients0108 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (9/128), (-79/512), (-105/512), (-767/4096), (-549/8192)]

def upper0108 : ℚ := (21287889/81920000000000)

def plusWeights0108 : Fin 11 → ℚ := ![(21287889/81920000000000), (21287889/8192000000000), (191591001/16384000000000), (63863667/2048000000000), (447045669/8192000000000), (1334737007/20480000000000), (434821669/8192000000000), (58008067/2048000000000), (146511001/16384000000000), (2075511/1638400000000), 0]

def minusWeights0108 : Fin 11 → ℚ := ![(21287889/81920000000000), (21287889/8192000000000), (191591001/16384000000000), (63863667/2048000000000), (447045669/8192000000000), (1347537007/20480000000000), (459269669/8192000000000), (69719267/2048000000000), (236671001/16384000000000), (32198223/8192000000000), (21287889/40960000000000)]

theorem checked0108 :
    (∀ i, 0 ≤ plusWeights0108 i) ∧
    (∀ i, 0 ≤ minusWeights0108 i) ∧
    (∀ i, plusCoefficients coefficients0108 upper0108 i = powerCoefficients10 plusWeights0108 i) ∧
    (∀ i, minusCoefficients coefficients0108 upper0108 i = powerCoefficients10 minusWeights0108 i) := by
  decide +kernel

theorem bound0108 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0108 g| ≤ (upper0108 : ℝ) :=
  abs_of_coefficients coefficients0108 upper0108 powerCoefficients10 plusWeights0108 minusWeights0108
    checked0108.1 checked0108.2.1 checked0108.2.2.1 checked0108.2.2.2
    (power_identity10 plusWeights0108) (power_identity10 minusWeights0108) g hg hmax

def envelope0108 : Envelope := ⟨coefficients0108, upper0108, bound0108⟩

def coefficients0109 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (1/1024), (77/8192), (1009/32768), (893/65536), (3365/524288)]

def upper0109 : ℚ := (304852559/1048576000000000)

def plusWeights0109 : Fin 11 → ℚ := ![(304852559/1048576000000000), (304852559/104857600000000), (2743673031/209715200000000), (914557677/26214400000000), (6401903739/104857600000000), (19128911217/262144000000000), (6248406139/104857600000000), (837884717/26214400000000), (2131157767/209715200000000), (760119219/524288000000000), 0]

def minusWeights0109 : Fin 11 → ℚ := ![(304852559/1048576000000000), (304852559/104857600000000), (2743673031/209715200000000), (914557677/26214400000000), (6401903739/104857600000000), (19282511217/262144000000000), (6555401339/104857600000000), (991230637/26214400000000), (671237659/41943040000000), (2288406371/524288000000000), (304852559/524288000000000)]

theorem checked0109 :
    (∀ i, 0 ≤ plusWeights0109 i) ∧
    (∀ i, 0 ≤ minusWeights0109 i) ∧
    (∀ i, plusCoefficients coefficients0109 upper0109 i = powerCoefficients10 plusWeights0109 i) ∧
    (∀ i, minusCoefficients coefficients0109 upper0109 i = powerCoefficients10 minusWeights0109 i) := by
  decide +kernel

theorem bound0109 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0109 g| ≤ (upper0109 : ℝ) :=
  abs_of_coefficients coefficients0109 upper0109 powerCoefficients10 plusWeights0109 minusWeights0109
    checked0109.1 checked0109.2.1 checked0109.2.2.1 checked0109.2.2.2
    (power_identity10 plusWeights0109) (power_identity10 minusWeights0109) g hg hmax

def envelope0109 : Envelope := ⟨coefficients0109, upper0109, bound0109⟩

def coefficients0110 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (29/2048), (67/4096), (1673/32768), (1461/65536), (2615/262144)]

def upper0110 : ℚ := (145038509/524288000000000)

def plusWeights0110 : Fin 11 → ℚ := ![(145038509/524288000000000), (145038509/52428800000000), (1305346581/104857600000000), (435115527/13107200000000), (3045808689/52428800000000), (9099026067/131072000000000), (2969751089/52428800000000), (397479367/13107200000000), (1007623477/104857600000000), (357600469/262144000000000), 0]

def minusWeights0110 : Fin 11 → ℚ := ![(145038509/524288000000000), (145038509/52428800000000), (1305346581/104857600000000), (435115527/13107200000000), (3045808689/52428800000000), (9175826067/131072000000000), (3121866289/52428800000000), (472751687/13107200000000), (320613937/20971520000000), (1092784621/262144000000000), (145038509/262144000000000)]

theorem checked0110 :
    (∀ i, 0 ≤ plusWeights0110 i) ∧
    (∀ i, 0 ≤ minusWeights0110 i) ∧
    (∀ i, plusCoefficients coefficients0110 upper0110 i = powerCoefficients10 plusWeights0110 i) ∧
    (∀ i, minusCoefficients coefficients0110 upper0110 i = powerCoefficients10 minusWeights0110 i) := by
  decide +kernel

theorem bound0110 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0110 g| ≤ (upper0110 : ℝ) :=
  abs_of_coefficients coefficients0110 upper0110 powerCoefficients10 plusWeights0110 minusWeights0110
    checked0110.1 checked0110.2.1 checked0110.2.2.1 checked0110.2.2.2
    (power_identity10 plusWeights0110) (power_identity10 minusWeights0110) g hg hmax

def envelope0110 : Envelope := ⟨coefficients0110, upper0110, bound0110⟩

def coefficients0111 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (17/1024), (57/4096), (939/16384), (983/32768), (295/16384)]

def upper0111 : ℚ := (4495289/16384000000000)

def plusWeights0111 : Fin 11 → ℚ := ![(4495289/16384000000000), (4495289/1638400000000), (40457601/3276800000000), (13485867/409600000000), (94401069/1638400000000), (282003207/4096000000000), (92028269/1638400000000), (12313637/409600000000), (31199559/3276800000000), (44257123/32768000000000), 0]

def minusWeights0111 : Fin 11 → ℚ := ![(4495289/16384000000000), (4495289/1638400000000), (40457601/3276800000000), (13485867/409600000000), (94401069/1638400000000), (284403207/4096000000000), (96773869/1638400000000), (14658097/409600000000), (49715643/3276800000000), (135554437/32768000000000), (4495289/8192000000000)]

theorem checked0111 :
    (∀ i, 0 ≤ plusWeights0111 i) ∧
    (∀ i, 0 ≤ minusWeights0111 i) ∧
    (∀ i, plusCoefficients coefficients0111 upper0111 i = powerCoefficients10 plusWeights0111 i) ∧
    (∀ i, minusCoefficients coefficients0111 upper0111 i = powerCoefficients10 minusWeights0111 i) := by
  decide +kernel

theorem bound0111 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0111 g| ≤ (upper0111 : ℝ) :=
  abs_of_coefficients coefficients0111 upper0111 powerCoefficients10 plusWeights0111 minusWeights0111
    checked0111.1 checked0111.2.1 checked0111.2.2.1 checked0111.2.2.2
    (power_identity10 plusWeights0111) (power_identity10 minusWeights0111) g hg hmax

def envelope0111 : Envelope := ⟨coefficients0111, upper0111, bound0111⟩

def coefficients0112 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (69/2048), (369/8192), (2703/32768), (2451/65536), (6105/262144)]

def upper0112 : ℚ := (133121091/524288000000000)

def plusWeights0112 : Fin 11 → ℚ := ![(133121091/524288000000000), (133121091/52428800000000), (1198089819/104857600000000), (399363273/13107200000000), (2795542911/52428800000000), (8348228733/131072000000000), (2720509311/52428800000000), (362788713/13107200000000), (36543603/4194304000000), (320918139/262144000000000), 0]

def minusWeights0112 : Fin 11 → ℚ := ![(133121091/524288000000000), (133121091/52428800000000), (1198089819/104857600000000), (399363273/13107200000000), (2795542911/52428800000000), (8425028733/131072000000000), (2870576511/52428800000000), (435937833/13107200000000), (1482589563/104857600000000), (1010292771/262144000000000), (133121091/262144000000000)]

theorem checked0112 :
    (∀ i, 0 ≤ plusWeights0112 i) ∧
    (∀ i, 0 ≤ minusWeights0112 i) ∧
    (∀ i, plusCoefficients coefficients0112 upper0112 i = powerCoefficients10 plusWeights0112 i) ∧
    (∀ i, minusCoefficients coefficients0112 upper0112 i = powerCoefficients10 minusWeights0112 i) := by
  decide +kernel

theorem bound0112 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0112 g| ≤ (upper0112 : ℝ) :=
  abs_of_coefficients coefficients0112 upper0112 powerCoefficients10 plusWeights0112 minusWeights0112
    checked0112.1 checked0112.2.1 checked0112.2.2.1 checked0112.2.2.2
    (power_identity10 plusWeights0112) (power_identity10 minusWeights0112) g hg hmax

def envelope0112 : Envelope := ⟨coefficients0112, upper0112, bound0112⟩

def coefficients0113 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (21/512), (117/4096), (471/4096), (69/1024), (9585/131072)]

def upper0113 : ℚ := (64978179/262144000000000)

def plusWeights0113 : Fin 11 → ℚ := ![(64978179/262144000000000), (64978179/26214400000000), (584803611/52428800000000), (194934537/6553600000000), (1364541759/26214400000000), (4074425277/65536000000000), (1327216959/26214400000000), (176828457/6553600000000), (444615579/52428800000000), (155828367/131072000000000), 0]

def minusWeights0113 : Fin 11 → ℚ := ![(64978179/262144000000000), (64978179/26214400000000), (584803611/52428800000000), (194934537/6553600000000), (1364541759/26214400000000), (4112825277/65536000000000), (1401866559/26214400000000), (213040617/6553600000000), (724991643/52428800000000), (493953423/131072000000000), (64978179/131072000000000)]

theorem checked0113 :
    (∀ i, 0 ≤ plusWeights0113 i) ∧
    (∀ i, 0 ≤ minusWeights0113 i) ∧
    (∀ i, plusCoefficients coefficients0113 upper0113 i = powerCoefficients10 plusWeights0113 i) ∧
    (∀ i, minusCoefficients coefficients0113 upper0113 i = powerCoefficients10 minusWeights0113 i) := by
  decide +kernel

theorem bound0113 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0113 g| ≤ (upper0113 : ℝ) :=
  abs_of_coefficients coefficients0113 upper0113 powerCoefficients10 plusWeights0113 minusWeights0113
    checked0113.1 checked0113.2.1 checked0113.2.2.1 checked0113.2.2.2
    (power_identity10 plusWeights0113) (power_identity10 minusWeights0113) g hg hmax

def envelope0113 : Envelope := ⟨coefficients0113, upper0113, bound0113⟩

def coefficients0114 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (99/2048), (249/8192), (3393/32768), (4701/65536), (22755/262144)]

def upper0114 : ℚ := (126077361/524288000000000)

def plusWeights0114 : Fin 11 → ℚ := ![(126077361/524288000000000), (126077361/52428800000000), (1134696249/104857600000000), (378232083/13107200000000), (2647624581/52428800000000), (7904473743/131072000000000), (2573358981/52428800000000), (342406323/13107200000000), (171794757/20971520000000), (300026889/262144000000000), 0]

def minusWeights0114 : Fin 11 → ℚ := ![(126077361/524288000000000), (126077361/52428800000000), (1134696249/104857600000000), (378232083/13107200000000), (2647624581/52428800000000), (7981273743/131072000000000), (2721890181/52428800000000), (414057843/13107200000000), (1410418713/104857600000000), (960746721/262144000000000), (126077361/262144000000000)]

theorem checked0114 :
    (∀ i, 0 ≤ plusWeights0114 i) ∧
    (∀ i, 0 ≤ minusWeights0114 i) ∧
    (∀ i, plusCoefficients coefficients0114 upper0114 i = powerCoefficients10 plusWeights0114 i) ∧
    (∀ i, minusCoefficients coefficients0114 upper0114 i = powerCoefficients10 minusWeights0114 i) := by
  decide +kernel

theorem bound0114 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0114 g| ≤ (upper0114 : ℝ) :=
  abs_of_coefficients coefficients0114 upper0114 powerCoefficients10 plusWeights0114 minusWeights0114
    checked0114.1 checked0114.2.1 checked0114.2.2.1 checked0114.2.2.2
    (power_identity10 plusWeights0114) (power_identity10 minusWeights0114) g hg hmax

def envelope0114 : Envelope := ⟨coefficients0114, upper0114, bound0114⟩

def coefficients0115 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-13/512), (-1/1024), (-267/8192), (-75/2048), (-2105/65536), (-1385/131072)]

def upper0115 : ℚ := (67775097/262144000000000)

def plusWeights0115 : Fin 11 → ℚ := ![(67775097/262144000000000), (67775097/26214400000000), (609975873/52428800000000), (203325291/6553600000000), (1423277037/26214400000000), (4253191111/65536000000000), (1389971437/26214400000000), (186638331/6553600000000), (476016833/52428800000000), (6823267/5242880000000), 0]

def minusWeights0115 : Fin 11 → ℚ := ![(67775097/262144000000000), (67775097/26214400000000), (609975873/52428800000000), (203325291/6553600000000), (1423277037/26214400000000), (4286471111/65536000000000), (1456582637/26214400000000), (220012251/6553600000000), (743934913/52428800000000), (101433859/26214400000000), (67775097/131072000000000)]

theorem checked0115 :
    (∀ i, 0 ≤ plusWeights0115 i) ∧
    (∀ i, 0 ≤ minusWeights0115 i) ∧
    (∀ i, plusCoefficients coefficients0115 upper0115 i = powerCoefficients10 plusWeights0115 i) ∧
    (∀ i, minusCoefficients coefficients0115 upper0115 i = powerCoefficients10 minusWeights0115 i) := by
  decide +kernel

theorem bound0115 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0115 g| ≤ (upper0115 : ℝ) :=
  abs_of_coefficients coefficients0115 upper0115 powerCoefficients10 plusWeights0115 minusWeights0115
    checked0115.1 checked0115.2.1 checked0115.2.2.1 checked0115.2.2.2
    (power_identity10 plusWeights0115) (power_identity10 minusWeights0115) g hg hmax

def envelope0115 : Envelope := ⟨coefficients0115, upper0115, bound0115⟩

def coefficients0116 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-29/512), (-689/4096), (-55/512), (-1401/8192), (-1147/16384)]

def upper0116 : ℚ := (50641167/163840000000000)

def plusWeights0116 : Fin 11 → ℚ := ![(50641167/163840000000000), (50641167/16384000000000), (455770503/32768000000000), (151923501/4096000000000), (1063464507/16384000000000), (3180793521/40960000000000), (1043336507/16384000000000), (141326601/4096000000000), (366145703/32768000000000), (5372873/3276800000000), 0]

def minusWeights0116 : Fin 11 → ℚ := ![(50641167/163840000000000), (50641167/16384000000000), (455770503/32768000000000), (151923501/4096000000000), (1063464507/16384000000000), (3199993521/40960000000000), (1083592507/16384000000000), (162520401/4096000000000), (545395303/32768000000000), (74417969/16384000000000), (50641167/81920000000000)]

theorem checked0116 :
    (∀ i, 0 ≤ plusWeights0116 i) ∧
    (∀ i, 0 ≤ minusWeights0116 i) ∧
    (∀ i, plusCoefficients coefficients0116 upper0116 i = powerCoefficients10 plusWeights0116 i) ∧
    (∀ i, minusCoefficients coefficients0116 upper0116 i = powerCoefficients10 minusWeights0116 i) := by
  decide +kernel

theorem bound0116 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0116 g| ≤ (upper0116 : ℝ) :=
  abs_of_coefficients coefficients0116 upper0116 powerCoefficients10 plusWeights0116 minusWeights0116
    checked0116.1 checked0116.2.1 checked0116.2.2.1 checked0116.2.2.2
    (power_identity10 plusWeights0116) (power_identity10 minusWeights0116) g hg hmax

def envelope0116 : Envelope := ⟨coefficients0116, upper0116, bound0116⟩

def coefficients0117 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-29/512), (-687/4096), (-201/2048), (-1603/8192), (-693/8192)]

def upper0117 : ℚ := (25311123/81920000000000)

def plusWeights0117 : Fin 11 → ℚ := ![(25311123/81920000000000), (25311123/8192000000000), (227800107/16384000000000), (75933369/2048000000000), (531533583/8192000000000), (1589800749/20480000000000), (521469583/8192000000000), (70635019/2048000000000), (182991627/16384000000000), (335631/204800000000), 0]

def minusWeights0117 : Fin 11 → ℚ := ![(25311123/81920000000000), (25311123/8192000000000), (227800107/16384000000000), (75933369/2048000000000), (531533583/8192000000000), (1599400749/20480000000000), (541597583/8192000000000), (81231719/2048000000000), (272608587/16384000000000), (18598503/4096000000000), (25311123/40960000000000)]

theorem checked0117 :
    (∀ i, 0 ≤ plusWeights0117 i) ∧
    (∀ i, 0 ≤ minusWeights0117 i) ∧
    (∀ i, plusCoefficients coefficients0117 upper0117 i = powerCoefficients10 plusWeights0117 i) ∧
    (∀ i, minusCoefficients coefficients0117 upper0117 i = powerCoefficients10 minusWeights0117 i) := by
  decide +kernel

theorem bound0117 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0117 g| ≤ (upper0117 : ℝ) :=
  abs_of_coefficients coefficients0117 upper0117 powerCoefficients10 plusWeights0117 minusWeights0117
    checked0117.1 checked0117.2.1 checked0117.2.2.1 checked0117.2.2.2
    (power_identity10 plusWeights0117) (power_identity10 minusWeights0117) g hg hmax

def envelope0117 : Envelope := ⟨coefficients0117, upper0117, bound0117⟩

def coefficients0118 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-29/512), (-413/4096), (-29/1024), (-321/4096), (-287/8192)]

def upper0118 : ℚ := (24695907/81920000000000)

def plusWeights0118 : Fin 11 → ℚ := ![(24695907/81920000000000), (24695907/8192000000000), (222263163/16384000000000), (74087721/2048000000000), (518614047/8192000000000), (1551042141/20480000000000), (508550047/8192000000000), (68803071/2048000000000), (177794923/16384000000000), (519473/327680000000), 0]

def minusWeights0118 : Fin 11 → ℚ := ![(24695907/81920000000000), (24695907/8192000000000), (222263163/16384000000000), (74087721/2048000000000), (518614047/8192000000000), (1560642141/20480000000000), (528678047/8192000000000), (79372371/2048000000000), (266731403/16384000000000), (36404989/8192000000000), (24695907/40960000000000)]

theorem checked0118 :
    (∀ i, 0 ≤ plusWeights0118 i) ∧
    (∀ i, 0 ≤ minusWeights0118 i) ∧
    (∀ i, plusCoefficients coefficients0118 upper0118 i = powerCoefficients10 plusWeights0118 i) ∧
    (∀ i, minusCoefficients coefficients0118 upper0118 i = powerCoefficients10 minusWeights0118 i) := by
  decide +kernel

theorem bound0118 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0118 g| ≤ (upper0118 : ℝ) :=
  abs_of_coefficients coefficients0118 upper0118 powerCoefficients10 plusWeights0118 minusWeights0118
    checked0118.1 checked0118.2.1 checked0118.2.2.1 checked0118.2.2.2
    (power_identity10 plusWeights0118) (power_identity10 minusWeights0118) g hg hmax

def envelope0118 : Envelope := ⟨coefficients0118, upper0118, bound0118⟩

def coefficients0119 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-29/512), (-393/4096), (-3/128), (-607/8192), (-549/16384)]

def upper0119 : ℚ := (49303089/163840000000000)

def plusWeights0119 : Fin 11 → ℚ := ![(49303089/163840000000000), (49303089/16384000000000), (443727801/32768000000000), (147909267/4096000000000), (1035364869/16384000000000), (3096494607/40960000000000), (1015236869/16384000000000), (137341967/4096000000000), (354840921/32768000000000), (5182119/3276800000000), 0]

def minusWeights0119 : Fin 11 → ℚ := ![(49303089/163840000000000), (49303089/16384000000000), (443727801/32768000000000), (147909267/4096000000000), (1035364869/16384000000000), (3115694607/40960000000000), (1055492869/16384000000000), (158476567/4096000000000), (532614681/32768000000000), (72695583/16384000000000), (49303089/81920000000000)]

theorem checked0119 :
    (∀ i, 0 ≤ plusWeights0119 i) ∧
    (∀ i, 0 ≤ minusWeights0119 i) ∧
    (∀ i, plusCoefficients coefficients0119 upper0119 i = powerCoefficients10 plusWeights0119 i) ∧
    (∀ i, minusCoefficients coefficients0119 upper0119 i = powerCoefficients10 minusWeights0119 i) := by
  decide +kernel

theorem bound0119 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0119 g| ≤ (upper0119 : ℝ) :=
  abs_of_coefficients coefficients0119 upper0119 powerCoefficients10 plusWeights0119 minusWeights0119
    checked0119.1 checked0119.2.1 checked0119.2.2.1 checked0119.2.2.2
    (power_identity10 plusWeights0119) (power_identity10 minusWeights0119) g hg hmax

def envelope0119 : Envelope := ⟨coefficients0119, upper0119, bound0119⟩

def coefficients0120 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-29/512), (-285/4096), (-67/2048), (-2855/32768), (-2555/65536)]

def upper0120 : ℚ := (39110811/131072000000000)

def plusWeights0120 : Fin 11 → ℚ := ![(39110811/131072000000000), (39110811/13107200000000), (351997299/26214400000000), (117332433/3276800000000), (821327031/13107200000000), (2456301093/32768000000000), (805224631/13107200000000), (108887233/3276800000000), (281092723/26214400000000), (20497893/13107200000000), 0]

def minusWeights0120 : Fin 11 → ℚ := ![(39110811/131072000000000), (39110811/13107200000000), (351997299/26214400000000), (117332433/3276800000000), (821327031/13107200000000), (2471661093/32768000000000), (837429431/13107200000000), (125777633/3276800000000), (676643/41943040000), (57723729/13107200000000), (39110811/65536000000000)]

theorem checked0120 :
    (∀ i, 0 ≤ plusWeights0120 i) ∧
    (∀ i, 0 ≤ minusWeights0120 i) ∧
    (∀ i, plusCoefficients coefficients0120 upper0120 i = powerCoefficients10 plusWeights0120 i) ∧
    (∀ i, minusCoefficients coefficients0120 upper0120 i = powerCoefficients10 minusWeights0120 i) := by
  decide +kernel

theorem bound0120 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0120 g| ≤ (upper0120 : ℝ) :=
  abs_of_coefficients coefficients0120 upper0120 powerCoefficients10 plusWeights0120 minusWeights0120
    checked0120.1 checked0120.2.1 checked0120.2.2.1 checked0120.2.2.2
    (power_identity10 plusWeights0120) (power_identity10 minusWeights0120) g hg hmax

def envelope0120 : Envelope := ⟨coefficients0120, upper0120, bound0120⟩

def coefficients0121 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-43/1024), (-661/8192), (-271/4096), (-587/8192), (-863/32768)]

def upper0121 : ℚ := (93445143/327680000000000)

def plusWeights0121 : Fin 11 → ℚ := ![(93445143/327680000000000), (93445143/32768000000000), (841006287/65536000000000), (280335429/8192000000000), (1962348003/32768000000000), (5867844009/81920000000000), (1922572003/32768000000000), (259693329/8192000000000), (669264527/65536000000000), (9740447/6553600000000), 0]

def minusWeights0121 : Fin 11 → ℚ := ![(93445143/327680000000000), (93445143/32768000000000), (841006287/65536000000000), (280335429/8192000000000), (1962348003/32768000000000), (5906244009/81920000000000), (2002124003/32768000000000), (300977529/8192000000000), (1012748047/65536000000000), (138188051/32768000000000), (93445143/163840000000000)]

theorem checked0121 :
    (∀ i, 0 ≤ plusWeights0121 i) ∧
    (∀ i, 0 ≤ minusWeights0121 i) ∧
    (∀ i, plusCoefficients coefficients0121 upper0121 i = powerCoefficients10 plusWeights0121 i) ∧
    (∀ i, minusCoefficients coefficients0121 upper0121 i = powerCoefficients10 minusWeights0121 i) := by
  decide +kernel

theorem bound0121 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0121 g| ≤ (upper0121 : ℝ) :=
  abs_of_coefficients coefficients0121 upper0121 powerCoefficients10 plusWeights0121 minusWeights0121
    checked0121.1 checked0121.2.1 checked0121.2.2.1 checked0121.2.2.2
    (power_identity10 plusWeights0121) (power_identity10 minusWeights0121) g hg hmax

def envelope0121 : Envelope := ⟨coefficients0121, upper0121, bound0121⟩

def coefficients0122 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-19/512), (-571/8192), (-27/512), (-5411/65536), (-4467/131072)]

def upper0122 : ℚ := (365779887/1310720000000000)

def plusWeights0122 : Fin 11 → ℚ := ![(365779887/1310720000000000), (365779887/131072000000000), (3292018983/262144000000000), (1097339661/32768000000000), (7681377627/131072000000000), (22967332881/327680000000000), (7522913627/131072000000000), (1015447261/32768000000000), (2613631143/262144000000000), (7593361/5242880000000), 0]

def minusWeights0122 : Fin 11 → ℚ := ![(365779887/1310720000000000), (365779887/131072000000000), (3292018983/262144000000000), (1097339661/32768000000000), (7681377627/131072000000000), (23120932881/327680000000000), (7839841627/131072000000000), (1179232061/32768000000000), (3970406823/262144000000000), (541725749/131072000000000), (365779887/655360000000000)]

theorem checked0122 :
    (∀ i, 0 ≤ plusWeights0122 i) ∧
    (∀ i, 0 ≤ minusWeights0122 i) ∧
    (∀ i, plusCoefficients coefficients0122 upper0122 i = powerCoefficients10 plusWeights0122 i) ∧
    (∀ i, minusCoefficients coefficients0122 upper0122 i = powerCoefficients10 minusWeights0122 i) := by
  decide +kernel

theorem bound0122 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0122 g| ≤ (upper0122 : ℝ) :=
  abs_of_coefficients coefficients0122 upper0122 powerCoefficients10 plusWeights0122 minusWeights0122
    checked0122.1 checked0122.2.1 checked0122.2.2.1 checked0122.2.2.2
    (power_identity10 plusWeights0122) (power_identity10 minusWeights0122) g hg hmax

def envelope0122 : Envelope := ⟨coefficients0122, upper0122, bound0122⟩

def coefficients0123 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-19/512), (-145/4096), (-17/2048), (-2405/32768), (-2305/65536)]

def upper0123 : ℚ := (36068961/131072000000000)

def plusWeights0123 : Fin 11 → ℚ := ![(36068961/131072000000000), (36068961/13107200000000), (324620649/26214400000000), (108206883/3276800000000), (757448181/13107200000000), (2264664543/32768000000000), (741601781/13107200000000), (100028883/3276800000000), (257063273/26214400000000), (18621023/13107200000000), 0]

def minusWeights0123 : Fin 11 → ℚ := ![(36068961/131072000000000), (36068961/13107200000000), (324620649/26214400000000), (108206883/3276800000000), (757448181/13107200000000), (2280024543/32768000000000), (773294581/13107200000000), (116384883/3276800000000), (15687121/1048576000000), (53516899/13107200000000), (36068961/65536000000000)]

theorem checked0123 :
    (∀ i, 0 ≤ plusWeights0123 i) ∧
    (∀ i, 0 ≤ minusWeights0123 i) ∧
    (∀ i, plusCoefficients coefficients0123 upper0123 i = powerCoefficients10 plusWeights0123 i) ∧
    (∀ i, minusCoefficients coefficients0123 upper0123 i = powerCoefficients10 minusWeights0123 i) := by
  decide +kernel

theorem bound0123 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0123 g| ≤ (upper0123 : ℝ) :=
  abs_of_coefficients coefficients0123 upper0123 powerCoefficients10 plusWeights0123 minusWeights0123
    checked0123.1 checked0123.2.1 checked0123.2.2.1 checked0123.2.2.2
    (power_identity10 plusWeights0123) (power_identity10 minusWeights0123) g hg hmax

def envelope0123 : Envelope := ⟨coefficients0123, upper0123, bound0123⟩

def coefficients0124 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/256), (-5/512), (-45/2048), (-5/512), (-35/4096), (-25/8192)]

def upper0124 : ℚ := (679549/3276800000000)

def plusWeights0124 : Fin 11 → ℚ := ![(679549/3276800000000), (679549/327680000000), (6115941/655360000000), (2038647/81920000000), (14270529/327680000000), (42651587/819200000000), (13947329/327680000000), (1875267/81920000000), (4793157/655360000000), (1722611/1638400000000), 0]

def minusWeights0124 : Fin 11 → ℚ := ![(679549/3276800000000), (679549/327680000000), (6115941/655360000000), (2038647/81920000000), (14270529/327680000000), (42971587/819200000000), (14593729/327680000000), (2202027/81920000000), (297549/26214400000), (5072879/1638400000000), (679549/1638400000000)]

theorem checked0124 :
    (∀ i, 0 ≤ plusWeights0124 i) ∧
    (∀ i, 0 ≤ minusWeights0124 i) ∧
    (∀ i, plusCoefficients coefficients0124 upper0124 i = powerCoefficients10 plusWeights0124 i) ∧
    (∀ i, minusCoefficients coefficients0124 upper0124 i = powerCoefficients10 minusWeights0124 i) := by
  decide +kernel

theorem bound0124 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0124 g| ≤ (upper0124 : ℝ) :=
  abs_of_coefficients coefficients0124 upper0124 powerCoefficients10 plusWeights0124 minusWeights0124
    checked0124.1 checked0124.2.1 checked0124.2.2.1 checked0124.2.2.2
    (power_identity10 plusWeights0124) (power_identity10 minusWeights0124) g hg hmax

def envelope0124 : Envelope := ⟨coefficients0124, upper0124, bound0124⟩

def coefficients0125 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/256), (-5/512), (-105/8192), (-15/4096), (-105/32768), (-75/65536)]

def upper0125 : ℚ := (5410647/26214400000000)

def plusWeights0125 : Fin 11 → ℚ := ![(5410647/26214400000000), (5410647/2621440000000), (48695823/5242880000000), (16231941/655360000000), (113623587/2621440000000), (339590761/6553600000000), (111037987/2621440000000), (14925501/655360000000), (38128271/5242880000000), (13689833/13107200000000), 0]

def minusWeights0125 : Fin 11 → ℚ := ![(5410647/26214400000000), (5410647/2621440000000), (48695823/5242880000000), (16231941/655360000000), (113623587/2621440000000), (342150761/6553600000000), (116209187/2621440000000), (17538381/655360000000), (474107/41943040000), (40416637/13107200000000), (5410647/13107200000000)]

theorem checked0125 :
    (∀ i, 0 ≤ plusWeights0125 i) ∧
    (∀ i, 0 ≤ minusWeights0125 i) ∧
    (∀ i, plusCoefficients coefficients0125 upper0125 i = powerCoefficients10 plusWeights0125 i) ∧
    (∀ i, minusCoefficients coefficients0125 upper0125 i = powerCoefficients10 minusWeights0125 i) := by
  decide +kernel

theorem bound0125 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0125 g| ≤ (upper0125 : ℝ) :=
  abs_of_coefficients coefficients0125 upper0125 powerCoefficients10 plusWeights0125 minusWeights0125
    checked0125.1 checked0125.2.1 checked0125.2.2.1 checked0125.2.2.2
    (power_identity10 plusWeights0125) (power_identity10 minusWeights0125) g hg hmax

def envelope0125 : Envelope := ⟨coefficients0125, upper0125, bound0125⟩

def coefficients0126 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-9/512), (-9/1024), (-61/2048), (-121/4096), (-745/32768), (-455/65536)]

def upper0126 : ℚ := (24624191/131072000000000)

def plusWeights0126 : Fin 11 → ℚ := ![(24624191/131072000000000), (24624191/13107200000000), (221617719/26214400000000), (73872573/3276800000000), (517108011/13107200000000), (1545564033/32768000000000), (505472811/13107200000000), (67987613/3276800000000), (34782667/5242880000000), (12518229/13107200000000), 0]

def minusWeights0126 : Fin 11 → ℚ := ![(24624191/131072000000000), (24624191/13107200000000), (221617719/26214400000000), (73872573/3276800000000), (517108011/13107200000000), (1557084033/32768000000000), (528743211/13107200000000), (79757533/3276800000000), (269322103/26214400000000), (36730153/13107200000000), (24624191/65536000000000)]

theorem checked0126 :
    (∀ i, 0 ≤ plusWeights0126 i) ∧
    (∀ i, 0 ≤ minusWeights0126 i) ∧
    (∀ i, plusCoefficients coefficients0126 upper0126 i = powerCoefficients10 plusWeights0126 i) ∧
    (∀ i, minusCoefficients coefficients0126 upper0126 i = powerCoefficients10 minusWeights0126 i) := by
  decide +kernel

theorem bound0126 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0126 g| ≤ (upper0126 : ℝ) :=
  abs_of_coefficients coefficients0126 upper0126 powerCoefficients10 plusWeights0126 minusWeights0126
    checked0126.1 checked0126.2.1 checked0126.2.2.1 checked0126.2.2.2
    (power_identity10 plusWeights0126) (power_identity10 minusWeights0126) g hg hmax

def envelope0126 : Envelope := ⟨coefficients0126, upper0126, bound0126⟩

def coefficients0127 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (1/1024), (-289/4096), (-327/4096), (-4537/65536), (-3149/131072)]

def upper0127 : ℚ := (213908289/1310720000000000)

def plusWeights0127 : Fin 11 → ℚ := ![(213908289/1310720000000000), (213908289/131072000000000), (1925174601/262144000000000), (641724867/32768000000000), (4492074069/131072000000000), (13425022207/327680000000000), (4389802069/131072000000000), (590421667/32768000000000), (1511352521/262144000000000), (21805507/26214400000000), 0]

def minusWeights0127 : Fin 11 → ℚ := ![(213908289/1310720000000000), (213908289/131072000000000), (1925174601/262144000000000), (641724867/32768000000000), (4492074069/131072000000000), (13527422207/327680000000000), (4594346069/131072000000000), (693028067/32768000000000), (2338996681/262144000000000), (318789043/131072000000000), (213908289/655360000000000)]

theorem checked0127 :
    (∀ i, 0 ≤ plusWeights0127 i) ∧
    (∀ i, 0 ≤ minusWeights0127 i) ∧
    (∀ i, plusCoefficients coefficients0127 upper0127 i = powerCoefficients10 plusWeights0127 i) ∧
    (∀ i, minusCoefficients coefficients0127 upper0127 i = powerCoefficients10 minusWeights0127 i) := by
  decide +kernel

theorem bound0127 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0127 g| ≤ (upper0127 : ℝ) :=
  abs_of_coefficients coefficients0127 upper0127 powerCoefficients10 plusWeights0127 minusWeights0127
    checked0127.1 checked0127.2.1 checked0127.2.2.1 checked0127.2.2.2
    (power_identity10 plusWeights0127) (power_identity10 minusWeights0127) g hg hmax

def envelope0127 : Envelope := ⟨coefficients0127, upper0127, bound0127⟩

end BilayerDressed.CubicQuarticEnvelopes

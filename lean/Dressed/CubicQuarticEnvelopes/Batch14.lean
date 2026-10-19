import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0448 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/512), (5/256), (1075/32768), (1415/65536), (4555/524288)]

def upper0448 : ℚ := (33135551/1048576000000000)

def plusWeights0448 : Fin 11 → ℚ := ![(33135551/1048576000000000), (33135551/104857600000000), (298219959/209715200000000), (99406653/26214400000000), (695846571/104857600000000), (2087539713/262144000000000), (698918571/104857600000000), (102529853/26214400000000), (336381559/209715200000000), (9221803/20971520000000), (33135551/524288000000000)]

def minusWeights0448 : Fin 11 → ℚ := ![(33135551/1048576000000000), (33135551/104857600000000), (298219959/209715200000000), (99406653/26214400000000), (695846571/104857600000000), (2087539713/262144000000000), (692774571/104857600000000), (96283453/26214400000000), (260058359/209715200000000), (20162087/104857600000000), 0]

theorem checked0448 :
    (∀ i, 0 ≤ plusWeights0448 i) ∧
    (∀ i, 0 ≤ minusWeights0448 i) ∧
    (∀ i, plusCoefficients coefficients0448 upper0448 i = powerCoefficients10 plusWeights0448 i) ∧
    (∀ i, minusCoefficients coefficients0448 upper0448 i = powerCoefficients10 minusWeights0448 i) := by
  decide +kernel

theorem bound0448 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0448 g| ≤ (upper0448 : ℝ) :=
  abs_of_coefficients coefficients0448 upper0448 powerCoefficients10 plusWeights0448 minusWeights0448
    checked0448.1 checked0448.2.1 checked0448.2.2.1 checked0448.2.2.2
    (power_identity10 plusWeights0448) (power_identity10 minusWeights0448) g hg hmax

def envelope0448 : Envelope := ⟨coefficients0448, upper0448, bound0448⟩

def coefficients0449 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/32), (369/8192), (101/4096), (3/128), (95/16384)]

def upper0449 : ℚ := (1180467/32768000000000)

def plusWeights0449 : Fin 11 → ℚ := ![(1180467/32768000000000), (1180467/3276800000000), (10624203/6553600000000), (3541401/819200000000), (24789807/3276800000000), (74369421/8192000000000), (24892207/3276800000000), (3647491/819200000000), (11943179/6553600000000), (8180199/16384000000000), (1180467/16384000000000)]

def minusWeights0449 : Fin 11 → ℚ := ![(1180467/32768000000000), (1180467/3276800000000), (10624203/6553600000000), (3541401/819200000000), (24789807/3276800000000), (74369421/8192000000000), (24687407/3276800000000), (3435311/819200000000), (9305227/6553600000000), (3624471/16384000000000), 0]

theorem checked0449 :
    (∀ i, 0 ≤ plusWeights0449 i) ∧
    (∀ i, 0 ≤ minusWeights0449 i) ∧
    (∀ i, plusCoefficients coefficients0449 upper0449 i = powerCoefficients10 plusWeights0449 i) ∧
    (∀ i, minusCoefficients coefficients0449 upper0449 i = powerCoefficients10 minusWeights0449 i) := by
  decide +kernel

theorem bound0449 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0449 g| ≤ (upper0449 : ℝ) :=
  abs_of_coefficients coefficients0449 upper0449 powerCoefficients10 plusWeights0449 minusWeights0449
    checked0449.1 checked0449.2.1 checked0449.2.2.1 checked0449.2.2.2
    (power_identity10 plusWeights0449) (power_identity10 minusWeights0449) g hg hmax

def envelope0449 : Envelope := ⟨coefficients0449, upper0449, bound0449⟩

def coefficients0450 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/32), (3/64), (47/512), (37/512), (35/2048)]

def upper0450 : ℚ := (151263/4096000000000)

def plusWeights0450 : Fin 11 → ℚ := ![(151263/4096000000000), (151263/409600000000), (1361367/819200000000), (453789/102400000000), (3176523/409600000000), (9529569/1024000000000), (3189323/409600000000), (467069/102400000000), (1527239/819200000000), (1045023/2048000000000), (151263/2048000000000)]

def minusWeights0450 : Fin 11 → ℚ := ![(151263/4096000000000), (151263/409600000000), (1361367/819200000000), (453789/102400000000), (3176523/409600000000), (9529569/1024000000000), (3163723/409600000000), (440509/102400000000), (239099/163840000000), (467607/2048000000000), 0]

theorem checked0450 :
    (∀ i, 0 ≤ plusWeights0450 i) ∧
    (∀ i, 0 ≤ minusWeights0450 i) ∧
    (∀ i, plusCoefficients coefficients0450 upper0450 i = powerCoefficients10 plusWeights0450 i) ∧
    (∀ i, minusCoefficients coefficients0450 upper0450 i = powerCoefficients10 minusWeights0450 i) := by
  decide +kernel

theorem bound0450 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0450 g| ≤ (upper0450 : ℝ) :=
  abs_of_coefficients coefficients0450 upper0450 powerCoefficients10 plusWeights0450 minusWeights0450
    checked0450.1 checked0450.2.1 checked0450.2.2.1 checked0450.2.2.2
    (power_identity10 plusWeights0450) (power_identity10 minusWeights0450) g hg hmax

def envelope0450 : Envelope := ⟨coefficients0450, upper0450, bound0450⟩

def coefficients0451 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/32), (3/64), (13/128), (21/256), (5/256)]

def upper0451 : ℚ := (18963/512000000000)

def plusWeights0451 : Fin 11 → ℚ := ![(18963/512000000000), (18963/51200000000), (170667/102400000000), (56889/12800000000), (398223/51200000000), (1194669/128000000000), (399823/51200000000), (58549/12800000000), (191411/102400000000), (32739/64000000000), (18963/256000000000)]

def minusWeights0451 : Fin 11 → ℚ := ![(18963/512000000000), (18963/51200000000), (170667/102400000000), (56889/12800000000), (398223/51200000000), (1194669/128000000000), (396623/51200000000), (55229/12800000000), (149923/102400000000), (29337/128000000000), 0]

theorem checked0451 :
    (∀ i, 0 ≤ plusWeights0451 i) ∧
    (∀ i, 0 ≤ minusWeights0451 i) ∧
    (∀ i, plusCoefficients coefficients0451 upper0451 i = powerCoefficients10 plusWeights0451 i) ∧
    (∀ i, minusCoefficients coefficients0451 upper0451 i = powerCoefficients10 minusWeights0451 i) := by
  decide +kernel

theorem bound0451 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0451 g| ≤ (upper0451 : ℝ) :=
  abs_of_coefficients coefficients0451 upper0451 powerCoefficients10 plusWeights0451 minusWeights0451
    checked0451.1 checked0451.2.1 checked0451.2.2.1 checked0451.2.2.2
    (power_identity10 plusWeights0451) (power_identity10 minusWeights0451) g hg hmax

def envelope0451 : Envelope := ⟨coefficients0451, upper0451, bound0451⟩

def coefficients0452 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/256), (131/4096), (83/4096), (93/4096), (95/16384)]

def upper0452 : ℚ := (1264203/32768000000000)

def plusWeights0452 : Fin 11 → ℚ := ![(1264203/32768000000000), (1264203/3276800000000), (11377827/6553600000000), (3792609/819200000000), (26548263/3276800000000), (79644789/8192000000000), (26663463/3276800000000), (3910429/819200000000), (2564887/1310720000000), (8789227/16384000000000), (1264203/16384000000000)]

def minusWeights0452 : Fin 11 → ℚ := ![(1264203/32768000000000), (1264203/3276800000000), (11377827/6553600000000), (3792609/819200000000), (26548263/3276800000000), (79644789/8192000000000), (26433063/3276800000000), (3674789/819200000000), (9931219/6553600000000), (3852803/16384000000000), 0]

theorem checked0452 :
    (∀ i, 0 ≤ plusWeights0452 i) ∧
    (∀ i, 0 ≤ minusWeights0452 i) ∧
    (∀ i, plusCoefficients coefficients0452 upper0452 i = powerCoefficients10 plusWeights0452 i) ∧
    (∀ i, minusCoefficients coefficients0452 upper0452 i = powerCoefficients10 minusWeights0452 i) := by
  decide +kernel

theorem bound0452 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0452 g| ≤ (upper0452 : ℝ) :=
  abs_of_coefficients coefficients0452 upper0452 powerCoefficients10 plusWeights0452 minusWeights0452
    checked0452.1 checked0452.2.1 checked0452.2.2.1 checked0452.2.2.2
    (power_identity10 plusWeights0452) (power_identity10 minusWeights0452) g hg hmax

def envelope0452 : Envelope := ⟨coefficients0452, upper0452, bound0452⟩

def coefficients0453 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (75/2048), (45/2048), (1755/32768), (2415/65536), (5565/262144)]

def upper0453 : ℚ := (20653233/524288000000000)

def plusWeights0453 : Fin 11 → ℚ := ![(20653233/524288000000000), (20653233/52428800000000), (185879097/104857600000000), (61959699/13107200000000), (433717893/52428800000000), (1301153679/131072000000000), (435637893/52428800000000), (63908499/13107200000000), (209666457/104857600000000), (1149477/2097152000000), (20653233/262144000000000)]

def minusWeights0453 : Fin 11 → ℚ := ![(20653233/524288000000000), (20653233/52428800000000), (185879097/104857600000000), (61959699/13107200000000), (433717893/52428800000000), (1301153679/131072000000000), (431797893/52428800000000), (60010899/13107200000000), (162091737/104857600000000), (12569541/52428800000000), 0]

theorem checked0453 :
    (∀ i, 0 ≤ plusWeights0453 i) ∧
    (∀ i, 0 ≤ minusWeights0453 i) ∧
    (∀ i, plusCoefficients coefficients0453 upper0453 i = powerCoefficients10 plusWeights0453 i) ∧
    (∀ i, minusCoefficients coefficients0453 upper0453 i = powerCoefficients10 minusWeights0453 i) := by
  decide +kernel

theorem bound0453 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0453 g| ≤ (upper0453 : ℝ) :=
  abs_of_coefficients coefficients0453 upper0453 powerCoefficients10 plusWeights0453 minusWeights0453
    checked0453.1 checked0453.2.1 checked0453.2.2.1 checked0453.2.2.2
    (power_identity10 plusWeights0453) (power_identity10 minusWeights0453) g hg hmax

def envelope0453 : Envelope := ⟨coefficients0453, upper0453, bound0453⟩

def coefficients0454 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/512), (207/4096), (39/1024), (63/2048), (15/2048)]

def upper0454 : ℚ := (190389/4096000000000)

def plusWeights0454 : Fin 11 → ℚ := ![(190389/4096000000000), (190389/409600000000), (1713501/819200000000), (571167/102400000000), (3998169/409600000000), (11994507/1024000000000), (4014969/409600000000), (1176969/204800000000), (1927833/819200000000), (660309/1024000000000), (190389/2048000000000)]

def minusWeights0454 : Fin 11 → ℚ := ![(190389/4096000000000), (190389/409600000000), (1713501/819200000000), (571167/102400000000), (3998169/409600000000), (11994507/1024000000000), (3981369/409600000000), (1107699/204800000000), (1499169/819200000000), (72909/256000000000), 0]

theorem checked0454 :
    (∀ i, 0 ≤ plusWeights0454 i) ∧
    (∀ i, 0 ≤ minusWeights0454 i) ∧
    (∀ i, plusCoefficients coefficients0454 upper0454 i = powerCoefficients10 plusWeights0454 i) ∧
    (∀ i, minusCoefficients coefficients0454 upper0454 i = powerCoefficients10 minusWeights0454 i) := by
  decide +kernel

theorem bound0454 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0454 g| ≤ (upper0454 : ℝ) :=
  abs_of_coefficients coefficients0454 upper0454 powerCoefficients10 plusWeights0454 minusWeights0454
    checked0454.1 checked0454.2.1 checked0454.2.2.1 checked0454.2.2.2
    (power_identity10 plusWeights0454) (power_identity10 minusWeights0454) g hg hmax

def envelope0454 : Envelope := ⟨coefficients0454, upper0454, bound0454⟩

def coefficients0455 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/512), (489/8192), (153/2048), (69/1024), (135/8192)]

def upper0455 : ℚ := (783171/16384000000000)

def plusWeights0455 : Fin 11 → ℚ := ![(783171/16384000000000), (783171/1638400000000), (7048539/3276800000000), (2349513/409600000000), (16446591/1638400000000), (49339773/4096000000000), (16513791/1638400000000), (1209579/204800000000), (7916067/3276800000000), (5419347/8192000000000), (783171/8192000000000)]

def minusWeights0455 : Fin 11 → ℚ := ![(783171/16384000000000), (783171/1638400000000), (7048539/3276800000000), (2349513/409600000000), (16446591/1638400000000), (49339773/4096000000000), (16379391/1638400000000), (569967/102400000000), (6181011/3276800000000), (2412363/8192000000000), 0]

theorem checked0455 :
    (∀ i, 0 ≤ plusWeights0455 i) ∧
    (∀ i, 0 ≤ minusWeights0455 i) ∧
    (∀ i, plusCoefficients coefficients0455 upper0455 i = powerCoefficients10 plusWeights0455 i) ∧
    (∀ i, minusCoefficients coefficients0455 upper0455 i = powerCoefficients10 minusWeights0455 i) := by
  decide +kernel

theorem bound0455 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0455 g| ≤ (upper0455 : ℝ) :=
  abs_of_coefficients coefficients0455 upper0455 powerCoefficients10 plusWeights0455 minusWeights0455
    checked0455.1 checked0455.2.1 checked0455.2.2.1 checked0455.2.2.2
    (power_identity10 plusWeights0455) (power_identity10 minusWeights0455) g hg hmax

def envelope0455 : Envelope := ⟨coefficients0455, upper0455, bound0455⟩

def coefficients0456 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/512), (357/4096), (39/1024), (63/2048), (15/2048)]

def upper0456 : ℚ := (205389/4096000000000)

def plusWeights0456 : Fin 11 → ℚ := ![(205389/4096000000000), (205389/409600000000), (1848501/819200000000), (616167/102400000000), (4313169/409600000000), (12939507/1024000000000), (4329969/409600000000), (1267719/204800000000), (2071833/819200000000), (709059/1024000000000), (205389/2048000000000)]

def minusWeights0456 : Fin 11 → ℚ := ![(205389/4096000000000), (205389/409600000000), (1848501/819200000000), (616167/102400000000), (4313169/409600000000), (12939507/1024000000000), (4296369/409600000000), (1196949/204800000000), (1625169/819200000000), (158943/512000000000), 0]

theorem checked0456 :
    (∀ i, 0 ≤ plusWeights0456 i) ∧
    (∀ i, 0 ≤ minusWeights0456 i) ∧
    (∀ i, plusCoefficients coefficients0456 upper0456 i = powerCoefficients10 plusWeights0456 i) ∧
    (∀ i, minusCoefficients coefficients0456 upper0456 i = powerCoefficients10 minusWeights0456 i) := by
  decide +kernel

theorem bound0456 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0456 g| ≤ (upper0456 : ℝ) :=
  abs_of_coefficients coefficients0456 upper0456 powerCoefficients10 plusWeights0456 minusWeights0456
    checked0456.1 checked0456.2.1 checked0456.2.2.1 checked0456.2.2.2
    (power_identity10 plusWeights0456) (power_identity10 minusWeights0456) g hg hmax

def envelope0456 : Envelope := ⟨coefficients0456, upper0456, bound0456⟩

def coefficients0457 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/512), (357/4096), (27/512), (93/2048), (45/4096)]

def upper0457 : ℚ := (412101/8192000000000)

def plusWeights0457 : Fin 11 → ℚ := ![(412101/8192000000000), (412101/819200000000), (3708909/1638400000000), (1236303/204800000000), (8654121/819200000000), (25962363/2048000000000), (8687721/819200000000), (158961/25600000000), (4155813/1638400000000), (2844111/4096000000000), (412101/4096000000000)]

def minusWeights0457 : Fin 11 → ℚ := ![(412101/8192000000000), (412101/819200000000), (3708909/1638400000000), (1236303/204800000000), (8654121/819200000000), (25962363/2048000000000), (8620521/819200000000), (600459/102400000000), (652401/327680000000), (1276899/4096000000000), 0]

theorem checked0457 :
    (∀ i, 0 ≤ plusWeights0457 i) ∧
    (∀ i, 0 ≤ minusWeights0457 i) ∧
    (∀ i, plusCoefficients coefficients0457 upper0457 i = powerCoefficients10 plusWeights0457 i) ∧
    (∀ i, minusCoefficients coefficients0457 upper0457 i = powerCoefficients10 minusWeights0457 i) := by
  decide +kernel

theorem bound0457 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0457 g| ≤ (upper0457 : ℝ) :=
  abs_of_coefficients coefficients0457 upper0457 powerCoefficients10 plusWeights0457 minusWeights0457
    checked0457.1 checked0457.2.1 checked0457.2.2.1 checked0457.2.2.2
    (power_identity10 plusWeights0457) (power_identity10 minusWeights0457) g hg hmax

def envelope0457 : Envelope := ⟨coefficients0457, upper0457, bound0457⟩

def coefficients0458 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/512), (357/4096), (153/2048), (69/1024), (135/8192)]

def upper0458 : ℚ := (828171/16384000000000)

def plusWeights0458 : Fin 11 → ℚ := ![(828171/16384000000000), (828171/1638400000000), (7453539/3276800000000), (2484513/409600000000), (17391591/1638400000000), (52174773/4096000000000), (17458791/1638400000000), (2555283/409600000000), (8348067/3276800000000), (5711847/8192000000000), (828171/8192000000000)]

def minusWeights0458 : Fin 11 → ℚ := ![(828171/16384000000000), (828171/1638400000000), (7453539/3276800000000), (2484513/409600000000), (17391591/1638400000000), (52174773/4096000000000), (17324391/1638400000000), (2413743/409600000000), (6559011/3276800000000), (2569863/8192000000000), 0]

theorem checked0458 :
    (∀ i, 0 ≤ plusWeights0458 i) ∧
    (∀ i, 0 ≤ minusWeights0458 i) ∧
    (∀ i, plusCoefficients coefficients0458 upper0458 i = powerCoefficients10 plusWeights0458 i) ∧
    (∀ i, minusCoefficients coefficients0458 upper0458 i = powerCoefficients10 minusWeights0458 i) := by
  decide +kernel

theorem bound0458 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0458 g| ≤ (upper0458 : ℝ) :=
  abs_of_coefficients coefficients0458 upper0458 powerCoefficients10 plusWeights0458 minusWeights0458
    checked0458.1 checked0458.2.1 checked0458.2.2.1 checked0458.2.2.2
    (power_identity10 plusWeights0458) (power_identity10 minusWeights0458) g hg hmax

def envelope0458 : Envelope := ⟨coefficients0458, upper0458, bound0458⟩

def coefficients0459 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (11/256), (273/8192), (41/2048), (61/2048), (65/8192)]

def upper0459 : ℚ := (762381/16384000000000)

def plusWeights0459 : Fin 11 → ℚ := ![(762381/16384000000000), (762381/1638400000000), (6861429/3276800000000), (2287143/409600000000), (16010001/1638400000000), (48030003/4096000000000), (16080401/1638400000000), (589727/102400000000), (1547929/655360000000), (5305329/8192000000000), (762381/8192000000000)]

def minusWeights0459 : Fin 11 → ℚ := ![(762381/16384000000000), (762381/1638400000000), (6861429/3276800000000), (2287143/409600000000), (16010001/1638400000000), (48030003/4096000000000), (15939601/1638400000000), (1107689/204800000000), (5983213/3276800000000), (2318481/8192000000000), 0]

theorem checked0459 :
    (∀ i, 0 ≤ plusWeights0459 i) ∧
    (∀ i, 0 ≤ minusWeights0459 i) ∧
    (∀ i, plusCoefficients coefficients0459 upper0459 i = powerCoefficients10 plusWeights0459 i) ∧
    (∀ i, minusCoefficients coefficients0459 upper0459 i = powerCoefficients10 minusWeights0459 i) := by
  decide +kernel

theorem bound0459 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0459 g| ≤ (upper0459 : ℝ) :=
  abs_of_coefficients coefficients0459 upper0459 powerCoefficients10 plusWeights0459 minusWeights0459
    checked0459.1 checked0459.2.1 checked0459.2.2.1 checked0459.2.2.2
    (power_identity10 plusWeights0459) (power_identity10 minusWeights0459) g hg hmax

def envelope0459 : Envelope := ⟨coefficients0459, upper0459, bound0459⟩

def coefficients0460 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (11/256), (273/8192), (71/2048), (91/2048), (95/8192)]

def upper0460 : ℚ := (765027/16384000000000)

def plusWeights0460 : Fin 11 → ℚ := ![(765027/16384000000000), (765027/1638400000000), (6885243/3276800000000), (2295081/409600000000), (16065567/1638400000000), (48196701/4096000000000), (16135967/1638400000000), (1183423/204800000000), (7763939/3276800000000), (5321079/8192000000000), (765027/8192000000000)]

def minusWeights0460 : Fin 11 → ℚ := ![(765027/16384000000000), (765027/1638400000000), (6885243/3276800000000), (2295081/409600000000), (16065567/1638400000000), (48196701/4096000000000), (15995167/1638400000000), (555829/102400000000), (6006547/3276800000000), (2329191/8192000000000), 0]

theorem checked0460 :
    (∀ i, 0 ≤ plusWeights0460 i) ∧
    (∀ i, 0 ≤ minusWeights0460 i) ∧
    (∀ i, plusCoefficients coefficients0460 upper0460 i = powerCoefficients10 plusWeights0460 i) ∧
    (∀ i, minusCoefficients coefficients0460 upper0460 i = powerCoefficients10 minusWeights0460 i) := by
  decide +kernel

theorem bound0460 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0460 g| ≤ (upper0460 : ℝ) :=
  abs_of_coefficients coefficients0460 upper0460 powerCoefficients10 plusWeights0460 minusWeights0460
    checked0460.1 checked0460.2.1 checked0460.2.2.1 checked0460.2.2.2
    (power_identity10 plusWeights0460) (power_identity10 minusWeights0460) g hg hmax

def envelope0460 : Envelope := ⟨coefficients0460, upper0460, bound0460⟩

def coefficients0461 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/1024), (15/512), (945/16384), (1245/32768), (2595/131072)]

def upper0461 : ℚ := (12449679/262144000000000)

def plusWeights0461 : Fin 11 → ℚ := ![(12449679/262144000000000), (12449679/26214400000000), (112047111/52428800000000), (37349037/6553600000000), (261443259/26214400000000), (784329777/65536000000000), (262595259/26214400000000), (38520237/6553600000000), (126362151/52428800000000), (3463863/5242880000000), (12449679/131072000000000)]

def minusWeights0461 : Fin 11 → ℚ := ![(12449679/262144000000000), (12449679/26214400000000), (112047111/52428800000000), (37349037/6553600000000), (261443259/26214400000000), (784329777/65536000000000), (260291259/26214400000000), (36177837/6553600000000), (97732071/52428800000000), (7580043/26214400000000), 0]

theorem checked0461 :
    (∀ i, 0 ≤ plusWeights0461 i) ∧
    (∀ i, 0 ≤ minusWeights0461 i) ∧
    (∀ i, plusCoefficients coefficients0461 upper0461 i = powerCoefficients10 plusWeights0461 i) ∧
    (∀ i, minusCoefficients coefficients0461 upper0461 i = powerCoefficients10 minusWeights0461 i) := by
  decide +kernel

theorem bound0461 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0461 g| ≤ (upper0461 : ℝ) :=
  abs_of_coefficients coefficients0461 upper0461 powerCoefficients10 plusWeights0461 minusWeights0461
    checked0461.1 checked0461.2.1 checked0461.2.2.1 checked0461.2.2.2
    (power_identity10 plusWeights0461) (power_identity10 minusWeights0461) g hg hmax

def envelope0461 : Envelope := ⟨coefficients0461, upper0461, bound0461⟩

def coefficients0462 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/1024), (15/512), (945/16384), (1245/32768), (33315/262144)]

def upper0462 : ℚ := (24904983/524288000000000)

def plusWeights0462 : Fin 11 → ℚ := ![(24904983/524288000000000), (24904983/52428800000000), (224144847/104857600000000), (74714949/13107200000000), (523004643/52428800000000), (1569013929/131072000000000), (525308643/52428800000000), (77057349/13107200000000), (252774927/104857600000000), (6928851/10485760000000), (24904983/262144000000000)]

def minusWeights0462 : Fin 11 → ℚ := ![(24904983/524288000000000), (24904983/52428800000000), (224144847/104857600000000), (74714949/13107200000000), (523004643/52428800000000), (1569013929/131072000000000), (520700643/52428800000000), (72372549/13107200000000), (195514767/104857600000000), (15165711/52428800000000), 0]

theorem checked0462 :
    (∀ i, 0 ≤ plusWeights0462 i) ∧
    (∀ i, 0 ≤ minusWeights0462 i) ∧
    (∀ i, plusCoefficients coefficients0462 upper0462 i = powerCoefficients10 plusWeights0462 i) ∧
    (∀ i, minusCoefficients coefficients0462 upper0462 i = powerCoefficients10 minusWeights0462 i) := by
  decide +kernel

theorem bound0462 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0462 g| ≤ (upper0462 : ℝ) :=
  abs_of_coefficients coefficients0462 upper0462 powerCoefficients10 plusWeights0462 minusWeights0462
    checked0462.1 checked0462.2.1 checked0462.2.2.1 checked0462.2.2.2
    (power_identity10 plusWeights0462) (power_identity10 minusWeights0462) g hg hmax

def envelope0462 : Envelope := ⟨coefficients0462, upper0462, bound0462⟩

def coefficients0463 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/1024), (15/512), (255/4096), (405/8192), (21765/262144)]

def upper0463 : ℚ := (24932673/524288000000000)

def plusWeights0463 : Fin 11 → ℚ := ![(24932673/524288000000000), (24932673/52428800000000), (224394057/104857600000000), (74798019/13107200000000), (523586133/52428800000000), (1570758399/131072000000000), (525890133/52428800000000), (77140419/13107200000000), (253028937/104857600000000), (6935469/10485760000000), (24932673/262144000000000)]

def minusWeights0463 : Fin 11 → ℚ := ![(24932673/524288000000000), (24932673/52428800000000), (224394057/104857600000000), (74798019/13107200000000), (523586133/52428800000000), (1570758399/131072000000000), (521282133/52428800000000), (72455619/13107200000000), (195759177/104857600000000), (15188001/52428800000000), 0]

theorem checked0463 :
    (∀ i, 0 ≤ plusWeights0463 i) ∧
    (∀ i, 0 ≤ minusWeights0463 i) ∧
    (∀ i, plusCoefficients coefficients0463 upper0463 i = powerCoefficients10 plusWeights0463 i) ∧
    (∀ i, minusCoefficients coefficients0463 upper0463 i = powerCoefficients10 minusWeights0463 i) := by
  decide +kernel

theorem bound0463 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0463 g| ≤ (upper0463 : ℝ) :=
  abs_of_coefficients coefficients0463 upper0463 powerCoefficients10 plusWeights0463 minusWeights0463
    checked0463.1 checked0463.2.1 checked0463.2.2.1 checked0463.2.2.2
    (power_identity10 plusWeights0463) (power_identity10 minusWeights0463) g hg hmax

def envelope0463 : Envelope := ⟨coefficients0463, upper0463, bound0463⟩

def coefficients0464 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/1024), (15/512), (1065/16384), (1485/32768), (1365/32768)]

def upper0464 : ℚ := (3117843/65536000000000)

def plusWeights0464 : Fin 11 → ℚ := ![(3117843/65536000000000), (3117843/6553600000000), (28060587/13107200000000), (9353529/1638400000000), (65474703/6553600000000), (196424109/16384000000000), (65762703/6553600000000), (9646329/1638400000000), (31640307/13107200000000), (216813/327680000000), (3117843/32768000000000)]

def minusWeights0464 : Fin 11 → ℚ := ![(3117843/65536000000000), (3117843/6553600000000), (28060587/13107200000000), (9353529/1638400000000), (65474703/6553600000000), (196424109/16384000000000), (65186703/6553600000000), (9060729/1638400000000), (24480867/13107200000000), (949713/3276800000000), 0]

theorem checked0464 :
    (∀ i, 0 ≤ plusWeights0464 i) ∧
    (∀ i, 0 ≤ minusWeights0464 i) ∧
    (∀ i, plusCoefficients coefficients0464 upper0464 i = powerCoefficients10 plusWeights0464 i) ∧
    (∀ i, minusCoefficients coefficients0464 upper0464 i = powerCoefficients10 minusWeights0464 i) := by
  decide +kernel

theorem bound0464 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0464 g| ≤ (upper0464 : ℝ) :=
  abs_of_coefficients coefficients0464 upper0464 powerCoefficients10 plusWeights0464 minusWeights0464
    checked0464.1 checked0464.2.1 checked0464.2.2.1 checked0464.2.2.2
    (power_identity10 plusWeights0464) (power_identity10 minusWeights0464) g hg hmax

def envelope0464 : Envelope := ⟨coefficients0464, upper0464, bound0464⟩

def coefficients0465 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/1024), (15/512), (2565/32768), (3765/65536), (41655/524288)]

def upper0465 : ℚ := (50041371/1048576000000000)

def plusWeights0465 : Fin 11 → ℚ := ![(50041371/1048576000000000), (50041371/104857600000000), (450372339/209715200000000), (150124113/26214400000000), (1050868791/104857600000000), (3152606373/262144000000000), (1055476791/104857600000000), (154808913/26214400000000), (507675699/209715200000000), (13913031/20971520000000), (50041371/524288000000000)]

def minusWeights0465 : Fin 11 → ℚ := ![(50041371/1048576000000000), (50041371/104857600000000), (450372339/209715200000000), (150124113/26214400000000), (1050868791/104857600000000), (3152606373/262144000000000), (1046260791/104857600000000), (145439313/26214400000000), (393068979/209715200000000), (30517587/104857600000000), 0]

theorem checked0465 :
    (∀ i, 0 ≤ plusWeights0465 i) ∧
    (∀ i, 0 ≤ minusWeights0465 i) ∧
    (∀ i, plusCoefficients coefficients0465 upper0465 i = powerCoefficients10 plusWeights0465 i) ∧
    (∀ i, minusCoefficients coefficients0465 upper0465 i = powerCoefficients10 minusWeights0465 i) := by
  decide +kernel

theorem bound0465 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0465 g| ≤ (upper0465 : ℝ) :=
  abs_of_coefficients coefficients0465 upper0465 powerCoefficients10 plusWeights0465 minusWeights0465
    checked0465.1 checked0465.2.1 checked0465.2.2.1 checked0465.2.2.2
    (power_identity10 plusWeights0465) (power_identity10 minusWeights0465) g hg hmax

def envelope0465 : Envelope := ⟨coefficients0465, upper0465, bound0465⟩

def coefficients0466 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (3/64), (9/128), (17/128), (53/512), (25/1024)]

def upper0466 : ℚ := (113337/2048000000000)

def plusWeights0466 : Fin 11 → ℚ := ![(113337/2048000000000), (113337/204800000000), (1020033/409600000000), (340011/51200000000), (2380077/204800000000), (7140231/512000000000), (2389677/204800000000), (349971/51200000000), (1144417/409600000000), (783111/1024000000000), (113337/1024000000000)]

def minusWeights0466 : Fin 11 → ℚ := ![(113337/2048000000000), (113337/204800000000), (1020033/409600000000), (340011/51200000000), (2380077/204800000000), (7140231/512000000000), (2370477/204800000000), (330051/51200000000), (895649/409600000000), (350259/1024000000000), 0]

theorem checked0466 :
    (∀ i, 0 ≤ plusWeights0466 i) ∧
    (∀ i, 0 ≤ minusWeights0466 i) ∧
    (∀ i, plusCoefficients coefficients0466 upper0466 i = powerCoefficients10 plusWeights0466 i) ∧
    (∀ i, minusCoefficients coefficients0466 upper0466 i = powerCoefficients10 minusWeights0466 i) := by
  decide +kernel

theorem bound0466 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0466 g| ≤ (upper0466 : ℝ) :=
  abs_of_coefficients coefficients0466 upper0466 powerCoefficients10 plusWeights0466 minusWeights0466
    checked0466.1 checked0466.2.1 checked0466.2.2.1 checked0466.2.2.2
    (power_identity10 plusWeights0466) (power_identity10 minusWeights0466) g hg hmax

def envelope0466 : Envelope := ⟨coefficients0466, upper0466, bound0466⟩

def coefficients0467 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (3/64), (9/128), (11/64), (73/512), (35/1024)]

def upper0467 : ℚ := (114219/2048000000000)

def plusWeights0467 : Fin 11 → ℚ := ![(114219/2048000000000), (114219/204800000000), (1027971/409600000000), (342657/51200000000), (2398599/204800000000), (7195797/512000000000), (2408199/204800000000), (352617/51200000000), (230503/81920000000), (788361/1024000000000), (114219/1024000000000)]

def minusWeights0467 : Fin 11 → ℚ := ![(114219/2048000000000), (114219/204800000000), (1027971/409600000000), (342657/51200000000), (2398599/204800000000), (7195797/512000000000), (2388999/204800000000), (332697/51200000000), (903427/409600000000), (353829/1024000000000), 0]

theorem checked0467 :
    (∀ i, 0 ≤ plusWeights0467 i) ∧
    (∀ i, 0 ≤ minusWeights0467 i) ∧
    (∀ i, plusCoefficients coefficients0467 upper0467 i = powerCoefficients10 plusWeights0467 i) ∧
    (∀ i, minusCoefficients coefficients0467 upper0467 i = powerCoefficients10 minusWeights0467 i) := by
  decide +kernel

theorem bound0467 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0467 g| ≤ (upper0467 : ℝ) :=
  abs_of_coefficients coefficients0467 upper0467 powerCoefficients10 plusWeights0467 minusWeights0467
    checked0467.1 checked0467.2.1 checked0467.2.2.1 checked0467.2.2.2
    (power_identity10 plusWeights0467) (power_identity10 minusWeights0467) g hg hmax

def envelope0467 : Envelope := ⟨coefficients0467, upper0467, bound0467⟩

def coefficients0468 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/512), (39/4096), (1653/16384), (1461/32768), (5355/262144)]

def upper0468 : ℚ := (28700607/524288000000000)

def plusWeights0468 : Fin 11 → ℚ := ![(28700607/524288000000000), (28700607/52428800000000), (258305463/104857600000000), (86101821/13107200000000), (602712747/52428800000000), (1808138241/131072000000000), (605477547/52428800000000), (88879101/13107200000000), (2335107/838860800000), (200088483/262144000000000), (28700607/262144000000000)]

def minusWeights0468 : Fin 11 → ℚ := ![(28700607/524288000000000), (28700607/52428800000000), (258305463/104857600000000), (86101821/13107200000000), (602712747/52428800000000), (1808138241/131072000000000), (599947947/52428800000000), (83324541/13107200000000), (224722551/104857600000000), (86917587/262144000000000), 0]

theorem checked0468 :
    (∀ i, 0 ≤ plusWeights0468 i) ∧
    (∀ i, 0 ≤ minusWeights0468 i) ∧
    (∀ i, plusCoefficients coefficients0468 upper0468 i = powerCoefficients10 plusWeights0468 i) ∧
    (∀ i, minusCoefficients coefficients0468 upper0468 i = powerCoefficients10 minusWeights0468 i) := by
  decide +kernel

theorem bound0468 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0468 g| ≤ (upper0468 : ℝ) :=
  abs_of_coefficients coefficients0468 upper0468 powerCoefficients10 plusWeights0468 minusWeights0468
    checked0468.1 checked0468.2.1 checked0468.2.2.1 checked0468.2.2.2
    (power_identity10 plusWeights0468) (power_identity10 minusWeights0468) g hg hmax

def envelope0468 : Envelope := ⟨coefficients0468, upper0468, bound0468⟩

def coefficients0469 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/256), (-51/512), (-69/512), (-2199/16384), (-1623/32768)]

def upper0469 : ℚ := (15448797/327680000000000)

def plusWeights0469 : Fin 11 → ℚ := ![(15448797/327680000000000), (15448797/32768000000000), (139039173/65536000000000), (46346391/8192000000000), (324424737/32768000000000), (973274211/81920000000000), (326344737/32768000000000), (48184791/8192000000000), (160032453/65536000000000), (22056879/32768000000000), (15448797/163840000000000)]

def minusWeights0469 : Fin 11 → ℚ := ![(15448797/327680000000000), (15448797/32768000000000), (139039173/65536000000000), (46346391/8192000000000), (324424737/32768000000000), (973274211/81920000000000), (322504737/32768000000000), (44507991/8192000000000), (118045893/65536000000000), (1768143/6553600000000), 0]

theorem checked0469 :
    (∀ i, 0 ≤ plusWeights0469 i) ∧
    (∀ i, 0 ≤ minusWeights0469 i) ∧
    (∀ i, plusCoefficients coefficients0469 upper0469 i = powerCoefficients10 plusWeights0469 i) ∧
    (∀ i, minusCoefficients coefficients0469 upper0469 i = powerCoefficients10 minusWeights0469 i) := by
  decide +kernel

theorem bound0469 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0469 g| ≤ (upper0469 : ℝ) :=
  abs_of_coefficients coefficients0469 upper0469 powerCoefficients10 plusWeights0469 minusWeights0469
    checked0469.1 checked0469.2.1 checked0469.2.2.1 checked0469.2.2.2
    (power_identity10 plusWeights0469) (power_identity10 minusWeights0469) g hg hmax

def envelope0469 : Envelope := ⟨coefficients0469, upper0469, bound0469⟩

def coefficients0470 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/256), (-15/512), (-15/256), (-135/4096), (-75/8192)]

def upper0470 : ℚ := (180369/3276800000000)

def plusWeights0470 : Fin 11 → ℚ := ![(180369/3276800000000), (180369/327680000000), (1623321/655360000000), (541107/81920000000), (3787749/327680000000), (11363247/819200000000), (3806949/327680000000), (560067/81920000000), (1847577/655360000000), (1269471/1638400000000), (180369/1638400000000)]

def minusWeights0470 : Fin 11 → ℚ := ![(180369/3276800000000), (180369/327680000000), (1623321/655360000000), (541107/81920000000), (3787749/327680000000), (11363247/819200000000), (3768549/327680000000), (522147/81920000000), (279813/131072000000), (534219/1638400000000), 0]

theorem checked0470 :
    (∀ i, 0 ≤ plusWeights0470 i) ∧
    (∀ i, 0 ≤ minusWeights0470 i) ∧
    (∀ i, plusCoefficients coefficients0470 upper0470 i = powerCoefficients10 plusWeights0470 i) ∧
    (∀ i, minusCoefficients coefficients0470 upper0470 i = powerCoefficients10 minusWeights0470 i) := by
  decide +kernel

theorem bound0470 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0470 g| ≤ (upper0470 : ℝ) :=
  abs_of_coefficients coefficients0470 upper0470 powerCoefficients10 plusWeights0470 minusWeights0470
    checked0470.1 checked0470.2.1 checked0470.2.2.1 checked0470.2.2.2
    (power_identity10 plusWeights0470) (power_identity10 minusWeights0470) g hg hmax

def envelope0470 : Envelope := ⟨coefficients0470, upper0470, bound0470⟩

def coefficients0471 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/16), (369/4096), (101/2048), (3/64), (95/8192)]

def upper0471 : ℚ := (1180467/16384000000000)

def plusWeights0471 : Fin 11 → ℚ := ![(1180467/16384000000000), (1180467/1638400000000), (10624203/3276800000000), (3541401/409600000000), (24789807/1638400000000), (74369421/4096000000000), (24892207/1638400000000), (3647491/409600000000), (11943179/3276800000000), (8180199/8192000000000), (1180467/8192000000000)]

def minusWeights0471 : Fin 11 → ℚ := ![(1180467/16384000000000), (1180467/1638400000000), (10624203/3276800000000), (3541401/409600000000), (24789807/1638400000000), (74369421/4096000000000), (24687407/1638400000000), (3435311/409600000000), (9305227/3276800000000), (3624471/8192000000000), 0]

theorem checked0471 :
    (∀ i, 0 ≤ plusWeights0471 i) ∧
    (∀ i, 0 ≤ minusWeights0471 i) ∧
    (∀ i, plusCoefficients coefficients0471 upper0471 i = powerCoefficients10 plusWeights0471 i) ∧
    (∀ i, minusCoefficients coefficients0471 upper0471 i = powerCoefficients10 minusWeights0471 i) := by
  decide +kernel

theorem bound0471 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0471 g| ≤ (upper0471 : ℝ) :=
  abs_of_coefficients coefficients0471 upper0471 powerCoefficients10 plusWeights0471 minusWeights0471
    checked0471.1 checked0471.2.1 checked0471.2.2.1 checked0471.2.2.2
    (power_identity10 plusWeights0471) (power_identity10 minusWeights0471) g hg hmax

def envelope0471 : Envelope := ⟨coefficients0471, upper0471, bound0471⟩

def coefficients0472 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/16), (369/4096), (163/1024), (321/2048), (5/128)]

def upper0472 : ℚ := (150039/2048000000000)

def plusWeights0472 : Fin 11 → ℚ := ![(150039/2048000000000), (150039/204800000000), (1350351/409600000000), (450117/51200000000), (3150819/204800000000), (9452457/512000000000), (3163619/204800000000), (1853513/204800000000), (1515673/409600000000), (2074581/2048000000000), (150039/1024000000000)]

def minusWeights0472 : Fin 11 → ℚ := ![(150039/2048000000000), (150039/204800000000), (1350351/409600000000), (450117/51200000000), (3150819/204800000000), (9452457/512000000000), (3138019/204800000000), (1747423/204800000000), (1185029/409600000000), (926199/2048000000000), 0]

theorem checked0472 :
    (∀ i, 0 ≤ plusWeights0472 i) ∧
    (∀ i, 0 ≤ minusWeights0472 i) ∧
    (∀ i, plusCoefficients coefficients0472 upper0472 i = powerCoefficients10 plusWeights0472 i) ∧
    (∀ i, minusCoefficients coefficients0472 upper0472 i = powerCoefficients10 minusWeights0472 i) := by
  decide +kernel

theorem bound0472 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0472 g| ≤ (upper0472 : ℝ) :=
  abs_of_coefficients coefficients0472 upper0472 powerCoefficients10 plusWeights0472 minusWeights0472
    checked0472.1 checked0472.2.1 checked0472.2.2.1 checked0472.2.2.2
    (power_identity10 plusWeights0472) (power_identity10 minusWeights0472) g hg hmax

def envelope0472 : Envelope := ⟨coefficients0472, upper0472, bound0472⟩

def coefficients0473 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/16), (3/32), (21/128), (1/8), (15/512)]

def upper0473 : ℚ := (75411/1024000000000)

def plusWeights0473 : Fin 11 → ℚ := ![(75411/1024000000000), (75411/102400000000), (678699/204800000000), (226233/25600000000), (1583631/102400000000), (4750893/256000000000), (1590031/102400000000), (232873/25600000000), (152319/40960000000), (521199/512000000000), (75411/512000000000)]

def minusWeights0473 : Fin 11 → ℚ := ![(75411/1024000000000), (75411/102400000000), (678699/204800000000), (226233/25600000000), (1583631/102400000000), (4750893/256000000000), (1577231/102400000000), (219593/25600000000), (595803/204800000000), (232911/512000000000), 0]

theorem checked0473 :
    (∀ i, 0 ≤ plusWeights0473 i) ∧
    (∀ i, 0 ≤ minusWeights0473 i) ∧
    (∀ i, plusCoefficients coefficients0473 upper0473 i = powerCoefficients10 plusWeights0473 i) ∧
    (∀ i, minusCoefficients coefficients0473 upper0473 i = powerCoefficients10 minusWeights0473 i) := by
  decide +kernel

theorem bound0473 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0473 g| ≤ (upper0473 : ℝ) :=
  abs_of_coefficients coefficients0473 upper0473 powerCoefficients10 plusWeights0473 minusWeights0473
    checked0473.1 checked0473.2.1 checked0473.2.2.1 checked0473.2.2.2
    (power_identity10 plusWeights0473) (power_identity10 minusWeights0473) g hg hmax

def envelope0473 : Envelope := ⟨coefficients0473, upper0473, bound0473⟩

def coefficients0474 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/16), (3/32), (31/128), (13/64), (25/512)]

def upper0474 : ℚ := (76293/1024000000000)

def plusWeights0474 : Fin 11 → ℚ := ![(76293/1024000000000), (76293/102400000000), (686637/204800000000), (228879/25600000000), (1602153/102400000000), (4806459/256000000000), (1608553/102400000000), (235519/25600000000), (769693/204800000000), (526449/512000000000), (76293/512000000000)]

def minusWeights0474 : Fin 11 → ℚ := ![(76293/1024000000000), (76293/102400000000), (686637/204800000000), (228879/25600000000), (1602153/102400000000), (4806459/256000000000), (1595753/102400000000), (222239/25600000000), (603581/204800000000), (236481/512000000000), 0]

theorem checked0474 :
    (∀ i, 0 ≤ plusWeights0474 i) ∧
    (∀ i, 0 ≤ minusWeights0474 i) ∧
    (∀ i, plusCoefficients coefficients0474 upper0474 i = powerCoefficients10 plusWeights0474 i) ∧
    (∀ i, minusCoefficients coefficients0474 upper0474 i = powerCoefficients10 minusWeights0474 i) := by
  decide +kernel

theorem bound0474 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0474 g| ≤ (upper0474 : ℝ) :=
  abs_of_coefficients coefficients0474 upper0474 powerCoefficients10 plusWeights0474 minusWeights0474
    checked0474.1 checked0474.2.1 checked0474.2.2.1 checked0474.2.2.2
    (power_identity10 plusWeights0474) (power_identity10 minusWeights0474) g hg hmax

def envelope0474 : Envelope := ⟨coefficients0474, upper0474, bound0474⟩

def coefficients0475 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (81/1024), (-27/2048), (1701/8192), (1587/16384), (17835/262144)]

def upper0475 : ℚ := (41923791/524288000000000)

def plusWeights0475 : Fin 11 → ℚ := ![(41923791/524288000000000), (41923791/52428800000000), (377314119/104857600000000), (125771373/13107200000000), (880399611/52428800000000), (2641198833/131072000000000), (884546811/52428800000000), (129901293/13107200000000), (426883527/104857600000000), (292640187/262144000000000), (41923791/262144000000000)]

def minusWeights0475 : Fin 11 → ℚ := ![(41923791/524288000000000), (41923791/52428800000000), (377314119/104857600000000), (125771373/13107200000000), (880399611/52428800000000), (2641198833/131072000000000), (876252411/52428800000000), (121641453/13107200000000), (327744711/104857600000000), (126597723/262144000000000), 0]

theorem checked0475 :
    (∀ i, 0 ≤ plusWeights0475 i) ∧
    (∀ i, 0 ≤ minusWeights0475 i) ∧
    (∀ i, plusCoefficients coefficients0475 upper0475 i = powerCoefficients10 plusWeights0475 i) ∧
    (∀ i, minusCoefficients coefficients0475 upper0475 i = powerCoefficients10 minusWeights0475 i) := by
  decide +kernel

theorem bound0475 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0475 g| ≤ (upper0475 : ℝ) :=
  abs_of_coefficients coefficients0475 upper0475 powerCoefficients10 plusWeights0475 minusWeights0475
    checked0475.1 checked0475.2.1 checked0475.2.2.1 checked0475.2.2.2
    (power_identity10 plusWeights0475) (power_identity10 minusWeights0475) g hg hmax

def envelope0475 : Envelope := ⟨coefficients0475, upper0475, bound0475⟩

def coefficients0476 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/256), (489/4096), (63/1024), (3/64), (45/4096)]

def upper0476 : ℚ := (775233/8192000000000)

def plusWeights0476 : Fin 11 → ℚ := ![(775233/8192000000000), (775233/819200000000), (6977097/1638400000000), (2325699/204800000000), (16279893/819200000000), (48839679/2048000000000), (16347093/819200000000), (149709/12800000000), (1568637/327680000000), (5372097/4096000000000), (775233/4096000000000)]

def minusWeights0476 : Fin 11 → ℚ := ![(775233/8192000000000), (775233/819200000000), (6977097/1638400000000), (2325699/204800000000), (16279893/819200000000), (48839679/2048000000000), (16212693/819200000000), (1128027/102400000000), (6111009/1638400000000), (2380233/4096000000000), 0]

theorem checked0476 :
    (∀ i, 0 ≤ plusWeights0476 i) ∧
    (∀ i, 0 ≤ minusWeights0476 i) ∧
    (∀ i, plusCoefficients coefficients0476 upper0476 i = powerCoefficients10 plusWeights0476 i) ∧
    (∀ i, minusCoefficients coefficients0476 upper0476 i = powerCoefficients10 minusWeights0476 i) := by
  decide +kernel

theorem bound0476 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0476 g| ≤ (upper0476 : ℝ) :=
  abs_of_coefficients coefficients0476 upper0476 powerCoefficients10 plusWeights0476 minusWeights0476
    checked0476.1 checked0476.2.1 checked0476.2.2.1 checked0476.2.2.2
    (power_identity10 plusWeights0476) (power_identity10 minusWeights0476) g hg hmax

def envelope0476 : Envelope := ⟨coefficients0476, upper0476, bound0476⟩

def coefficients0477 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (43/512), (381/4096), (239/2048), (61/512), (245/8192)]

def upper0477 : ℚ := (1549521/16384000000000)

def plusWeights0477 : Fin 11 → ℚ := ![(1549521/16384000000000), (1549521/1638400000000), (13945689/3276800000000), (4648563/409600000000), (32539941/1638400000000), (97619823/4096000000000), (32677541/1638400000000), (4789973/409600000000), (15692153/3276800000000), (10748301/8192000000000), (1549521/8192000000000)]

def minusWeights0477 : Fin 11 → ℚ := ![(1549521/16384000000000), (1549521/1638400000000), (13945689/3276800000000), (4648563/409600000000), (32539941/1638400000000), (97619823/4096000000000), (32402341/1638400000000), (4507153/409600000000), (487969/131072000000), (4746909/8192000000000), 0]

theorem checked0477 :
    (∀ i, 0 ≤ plusWeights0477 i) ∧
    (∀ i, 0 ≤ minusWeights0477 i) ∧
    (∀ i, plusCoefficients coefficients0477 upper0477 i = powerCoefficients10 plusWeights0477 i) ∧
    (∀ i, minusCoefficients coefficients0477 upper0477 i = powerCoefficients10 minusWeights0477 i) := by
  decide +kernel

theorem bound0477 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0477 g| ≤ (upper0477 : ℝ) :=
  abs_of_coefficients coefficients0477 upper0477 powerCoefficients10 plusWeights0477 minusWeights0477
    checked0477.1 checked0477.2.1 checked0477.2.2.1 checked0477.2.2.2
    (power_identity10 plusWeights0477) (power_identity10 minusWeights0477) g hg hmax

def envelope0477 : Envelope := ⟨coefficients0477, upper0477, bound0477⟩

def coefficients0478 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/512), (15/256), (945/16384), (1425/32768), (2775/262144)]

def upper0478 : ℚ := (9895551/104857600000000)

def plusWeights0478 : Fin 11 → ℚ := ![(9895551/104857600000000), (9895551/10485760000000), (89059959/20971520000000), (29686653/2621440000000), (207806571/10485760000000), (623419713/26214400000000), (208728171/10485760000000), (30623613/2621440000000), (20099979/4194304000000), (13778823/10485760000000), (9895551/52428800000000)]

def minusWeights0478 : Fin 11 → ℚ := ![(9895551/104857600000000), (9895551/10485760000000), (89059959/20971520000000), (29686653/2621440000000), (207806571/10485760000000), (623419713/26214400000000), (206884971/10485760000000), (28749693/2621440000000), (77620023/20971520000000), (6012279/10485760000000), 0]

theorem checked0478 :
    (∀ i, 0 ≤ plusWeights0478 i) ∧
    (∀ i, 0 ≤ minusWeights0478 i) ∧
    (∀ i, plusCoefficients coefficients0478 upper0478 i = powerCoefficients10 plusWeights0478 i) ∧
    (∀ i, minusCoefficients coefficients0478 upper0478 i = powerCoefficients10 minusWeights0478 i) := by
  decide +kernel

theorem bound0478 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0478 g| ≤ (upper0478 : ℝ) :=
  abs_of_coefficients coefficients0478 upper0478 powerCoefficients10 plusWeights0478 minusWeights0478
    checked0478.1 checked0478.2.1 checked0478.2.2.1 checked0478.2.2.2
    (power_identity10 plusWeights0478) (power_identity10 minusWeights0478) g hg hmax

def envelope0478 : Envelope := ⟨coefficients0478, upper0478, bound0478⟩

def coefficients0479 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (3/32), (9/64), (63/256), (3/16), (45/1024)]

def upper0479 : ℚ := (226233/2048000000000)

def plusWeights0479 : Fin 11 → ℚ := ![(226233/2048000000000), (226233/204800000000), (2036097/409600000000), (678699/51200000000), (4750893/204800000000), (14252679/512000000000), (4770093/204800000000), (698619/51200000000), (456957/81920000000), (1563597/1024000000000), (226233/1024000000000)]

def minusWeights0479 : Fin 11 → ℚ := ![(226233/2048000000000), (226233/204800000000), (2036097/409600000000), (678699/51200000000), (4750893/204800000000), (14252679/512000000000), (4731693/204800000000), (658779/51200000000), (1787409/409600000000), (698733/1024000000000), 0]

theorem checked0479 :
    (∀ i, 0 ≤ plusWeights0479 i) ∧
    (∀ i, 0 ≤ minusWeights0479 i) ∧
    (∀ i, plusCoefficients coefficients0479 upper0479 i = powerCoefficients10 plusWeights0479 i) ∧
    (∀ i, minusCoefficients coefficients0479 upper0479 i = powerCoefficients10 minusWeights0479 i) := by
  decide +kernel

theorem bound0479 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0479 g| ≤ (upper0479 : ℝ) :=
  abs_of_coefficients coefficients0479 upper0479 powerCoefficients10 plusWeights0479 minusWeights0479
    checked0479.1 checked0479.2.1 checked0479.2.2.1 checked0479.2.2.2
    (power_identity10 plusWeights0479) (power_identity10 minusWeights0479) g hg hmax

def envelope0479 : Envelope := ⟨coefficients0479, upper0479, bound0479⟩

end BilayerDressed.CubicQuarticEnvelopes

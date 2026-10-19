import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0064 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (-1/16), (-81/512), (-117/1024), (-821/4096), (-185/1024), (-999/8192), (-147/4096)]

def upper0064 : ℚ := (1443190071/20480000000000)

def plusWeights0064 : Fin 11 → ℚ := ![(1443190071/20480000000000), (1443190071/2048000000000), (12988710639/4096000000000), (4297570213/512000000000), (29398191491/2048000000000), (84000874473/5120000000000), (25618557491/2048000000000), (6274451901/1024000000000), (7160848939/4096000000000), (362498617/1638400000000), 0]

def minusWeights0064 : Fin 11 → ℚ := ![(1443190071/20480000000000), (1443190071/2048000000000), (12988710639/4096000000000), (4361570213/512000000000), (31215791491/2048000000000), (97841074473/5120000000000), (34995425491/2048000000000), (11043828951/1024000000000), (18816572339/4096000000000), (9733027483/8192000000000), (1443190071/10240000000000)]

theorem checked0064 :
    (∀ i, 0 ≤ plusWeights0064 i) ∧
    (∀ i, 0 ≤ minusWeights0064 i) ∧
    (∀ i, plusCoefficients coefficients0064 upper0064 i = powerCoefficients10 plusWeights0064 i) ∧
    (∀ i, minusCoefficients coefficients0064 upper0064 i = powerCoefficients10 minusWeights0064 i) := by
  decide +kernel

theorem bound0064 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0064 g| ≤ (upper0064 : ℝ) :=
  abs_of_coefficients coefficients0064 upper0064 powerCoefficients10 plusWeights0064 minusWeights0064
    checked0064.1 checked0064.2.1 checked0064.2.2.1 checked0064.2.2.2
    (power_identity10 plusWeights0064) (power_identity10 minusWeights0064) g hg hmax

def envelope0064 : Envelope := ⟨coefficients0064, upper0064, bound0064⟩

def coefficients0065 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (-1/16), (-39/256), (-59/512), (-387/2048), (-179/1024), (-873/8192), (-471/16384)]

def upper0065 : ℚ := (11535880331/163840000000000)

def plusWeights0065 : Fin 11 → ℚ := ![(11535880331/163840000000000), (11535880331/16384000000000), (103822922979/32768000000000), (34351640993/4096000000000), (234983086951/16384000000000), (671402060853/40960000000000), (204750798951/16384000000000), (25071275593/4096000000000), (57219152099/32768000000000), (724028101/3276800000000), 0]

def minusWeights0065 : Fin 11 → ℚ := ![(11535880331/163840000000000), (11535880331/16384000000000), (103822922979/32768000000000), (34863640993/4096000000000), (249523886951/16384000000000), (782118860853/40960000000000), (279756174951/16384000000000), (44144006393/4096000000000), (150426693859/32768000000000), (19451620157/16384000000000), (11535880331/81920000000000)]

theorem checked0065 :
    (∀ i, 0 ≤ plusWeights0065 i) ∧
    (∀ i, 0 ≤ minusWeights0065 i) ∧
    (∀ i, plusCoefficients coefficients0065 upper0065 i = powerCoefficients10 plusWeights0065 i) ∧
    (∀ i, minusCoefficients coefficients0065 upper0065 i = powerCoefficients10 minusWeights0065 i) := by
  decide +kernel

theorem bound0065 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0065 g| ≤ (upper0065 : ℝ) :=
  abs_of_coefficients coefficients0065 upper0065 powerCoefficients10 plusWeights0065 minusWeights0065
    checked0065.1 checked0065.2.1 checked0065.2.2.1 checked0065.2.2.2
    (power_identity10 plusWeights0065) (power_identity10 minusWeights0065) g hg hmax

def envelope0065 : Envelope := ⟨coefficients0065, upper0065, bound0065⟩

def coefficients0066 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (-1/16), (-35/256), (-55/512), (-329/2048), (-67/512), (-335/4096), (-195/8192)]

def upper0066 : ℚ := (1150846019/16384000000000)

def plusWeights0066 : Fin 11 → ℚ := ![(1150846019/16384000000000), (1150846019/1638400000000), (10357614171/3276800000000), (3426938057/409600000000), (23440726399/1638400000000), (66968099197/4096000000000), (20418790399/1638400000000), (2499555477/409600000000), (5702539963/3276800000000), (360618637/1638400000000), 0]

def minusWeights0066 : Fin 11 → ℚ := ![(1150846019/16384000000000), (1150846019/1638400000000), (10357614171/3276800000000), (3478138057/409600000000), (24894806399/1638400000000), (78038499197/4096000000000), (27916742399/1638400000000), (4405520637/409600000000), (15012688379/3276800000000), (1941073401/1638400000000), (1150846019/8192000000000)]

theorem checked0066 :
    (∀ i, 0 ≤ plusWeights0066 i) ∧
    (∀ i, 0 ≤ minusWeights0066 i) ∧
    (∀ i, plusCoefficients coefficients0066 upper0066 i = powerCoefficients10 plusWeights0066 i) ∧
    (∀ i, minusCoefficients coefficients0066 upper0066 i = powerCoefficients10 minusWeights0066 i) := by
  decide +kernel

theorem bound0066 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0066 g| ≤ (upper0066 : ℝ) :=
  abs_of_coefficients coefficients0066 upper0066 powerCoefficients10 plusWeights0066 minusWeights0066
    checked0066.1 checked0066.2.1 checked0066.2.2.1 checked0066.2.2.2
    (power_identity10 plusWeights0066) (power_identity10 minusWeights0066) g hg hmax

def envelope0066 : Envelope := ⟨coefficients0066, upper0066, bound0066⟩

def coefficients0067 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (-1/16), (-53/512), (-61/1024), (-915/8192), (-115/1024), (-2261/32768), (-1197/65536)]

def upper0067 : ℚ := (45781542417/655360000000000)

def plusWeights0067 : Fin 11 → ℚ := ![(45781542417/655360000000000), (45781542417/65536000000000), (412033881753/131072000000000), (136320627251/16384000000000), (932330790757/65536000000000), (2662883572271/163840000000000), (811565286757/65536000000000), (99282940251/16384000000000), (226305694553/131072000000000), (2858955739/13107200000000), 0]

def minusWeights0067 : Fin 11 → ℚ := ![(45781542417/655360000000000), (45781542417/65536000000000), (412033881753/131072000000000), (138368627251/16384000000000), (990493990757/65536000000000), (3105590772271/163840000000000), (1111259494757/65536000000000), (175406314251/16384000000000), (597762068953/131072000000000), (77268306139/65536000000000), (45781542417/327680000000000)]

theorem checked0067 :
    (∀ i, 0 ≤ plusWeights0067 i) ∧
    (∀ i, 0 ≤ minusWeights0067 i) ∧
    (∀ i, plusCoefficients coefficients0067 upper0067 i = powerCoefficients10 plusWeights0067 i) ∧
    (∀ i, minusCoefficients coefficients0067 upper0067 i = powerCoefficients10 minusWeights0067 i) := by
  decide +kernel

theorem bound0067 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0067 g| ≤ (upper0067 : ℝ) :=
  abs_of_coefficients coefficients0067 upper0067 powerCoefficients10 plusWeights0067 minusWeights0067
    checked0067.1 checked0067.2.1 checked0067.2.2.1 checked0067.2.2.2
    (power_identity10 plusWeights0067) (power_identity10 minusWeights0067) g hg hmax

def envelope0067 : Envelope := ⟨coefficients0067, upper0067, bound0067⟩

def coefficients0068 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (1/32), (-1/64), (143/1024), (83/512), (2755/16384), (2295/32768), (2925/131072)]

def upper0068 : ℚ := (3112888531/52428800000000)

def plusWeights0068 : Fin 11 → ℚ := ![(3112888531/52428800000000), (3112888531/5242880000000), (28015996779/10485760000000), (9256745593/1310720000000), (63093283151/5242880000000), (179152489453/13107200000000), (54144255311/5242880000000), (6552091001/1310720000000), (14737886283/10485760000000), (4582690731/26214400000000), 0]

def minusWeights0068 : Fin 11 → ℚ := ![(3112888531/52428800000000), (3112888531/5242880000000), (28015996779/10485760000000), (9420585593/1310720000000), (67648035151/5242880000000), (213071465453/13107200000000), (76597062991/5242880000000), (2425048037/262144000000), (1651764291/419430400000), (26546194579/26214400000000), (3112888531/26214400000000)]

theorem checked0068 :
    (∀ i, 0 ≤ plusWeights0068 i) ∧
    (∀ i, 0 ≤ minusWeights0068 i) ∧
    (∀ i, plusCoefficients coefficients0068 upper0068 i = powerCoefficients10 plusWeights0068 i) ∧
    (∀ i, minusCoefficients coefficients0068 upper0068 i = powerCoefficients10 minusWeights0068 i) := by
  decide +kernel

theorem bound0068 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0068 g| ≤ (upper0068 : ℝ) :=
  abs_of_coefficients coefficients0068 upper0068 powerCoefficients10 plusWeights0068 minusWeights0068
    checked0068.1 checked0068.2.1 checked0068.2.2.1 checked0068.2.2.2
    (power_identity10 plusWeights0068) (power_identity10 minusWeights0068) g hg hmax

def envelope0068 : Envelope := ⟨coefficients0068, upper0068, bound0068⟩

def coefficients0069 : Fin 11 → ℚ := ![0, 0, 0, (-1/16), (1/32), (3/128), (167/1024), (643/4096), (2423/16384), (2411/32768), (2905/131072)]

def upper0069 : ℚ := (15456085251/262144000000000)

def plusWeights0069 : Fin 11 → ℚ := ![(15456085251/262144000000000), (15456085251/26214400000000), (139104767259/52428800000000), (45958655753/6553600000000), (313190910271/26214400000000), (888961530813/65536000000000), (268497585471/26214400000000), (32461593833/6553600000000), (14585259263/10485760000000), (22639700379/131072000000000), 0]

def minusWeights0069 : Fin 11 → ℚ := ![(15456085251/262144000000000), (15456085251/26214400000000), (139104767259/52428800000000), (46777855753/6553600000000), (335964670271/26214400000000), (1058505210813/65536000000000), (380657995071/26214400000000), (60274917673/6553600000000), (205283238203/52428800000000), (131921152131/131072000000000), (15456085251/131072000000000)]

theorem checked0069 :
    (∀ i, 0 ≤ plusWeights0069 i) ∧
    (∀ i, 0 ≤ minusWeights0069 i) ∧
    (∀ i, plusCoefficients coefficients0069 upper0069 i = powerCoefficients10 plusWeights0069 i) ∧
    (∀ i, minusCoefficients coefficients0069 upper0069 i = powerCoefficients10 minusWeights0069 i) := by
  decide +kernel

theorem bound0069 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0069 g| ≤ (upper0069 : ℝ) :=
  abs_of_coefficients coefficients0069 upper0069 powerCoefficients10 plusWeights0069 minusWeights0069
    checked0069.1 checked0069.2.1 checked0069.2.2.1 checked0069.2.2.2
    (power_identity10 plusWeights0069) (power_identity10 minusWeights0069) g hg hmax

def envelope0069 : Envelope := ⟨coefficients0069, upper0069, bound0069⟩

def coefficients0070 : Fin 11 → ℚ := ![0, 0, 0, (-1/32), (1/128), (3/128), (145/2048), (475/8192), (1717/32768), (1629/65536), (4145/524288)]

def upper0070 : ℚ := (31622143667/1048576000000000)

def plusWeights0070 : Fin 11 → ℚ := ![(31622143667/1048576000000000), (31622143667/104857600000000), (284599293003/209715200000000), (94047231001/26214400000000), (641209337007/104857600000000), (1821453291021/262144000000000), (550736121007/104857600000000), (66673047001/26214400000000), (150015658891/209715200000000), (46652880807/524288000000000), 0]

def minusWeights0070 : Fin 11 → ℚ := ![(31622143667/1048576000000000), (31622143667/104857600000000), (284599293003/209715200000000), (95685631001/26214400000000), (686920697007/104857600000000), (2162936811021/262144000000000), (777393913007/104857600000000), (123059815001/26214400000000), (83836585423/41943040000000), (269568555863/524288000000000), (31622143667/524288000000000)]

theorem checked0070 :
    (∀ i, 0 ≤ plusWeights0070 i) ∧
    (∀ i, 0 ≤ minusWeights0070 i) ∧
    (∀ i, plusCoefficients coefficients0070 upper0070 i = powerCoefficients10 plusWeights0070 i) ∧
    (∀ i, minusCoefficients coefficients0070 upper0070 i = powerCoefficients10 minusWeights0070 i) := by
  decide +kernel

theorem bound0070 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0070 g| ≤ (upper0070 : ℝ) :=
  abs_of_coefficients coefficients0070 upper0070 powerCoefficients10 plusWeights0070 minusWeights0070
    checked0070.1 checked0070.2.1 checked0070.2.2.1 checked0070.2.2.2
    (power_identity10 plusWeights0070) (power_identity10 minusWeights0070) g hg hmax

def envelope0070 : Envelope := ⟨coefficients0070, upper0070, bound0070⟩

def coefficients0071 : Fin 11 → ℚ := ![0, 0, 0, (-1/32), (1/32), (25/512), (59/512), (307/4096), (3187/32768), (3999/65536), (14825/524288)]

def upper0071 : ℚ := (28849422011/1048576000000000)

def plusWeights0071 : Fin 11 → ℚ := ![(28849422011/1048576000000000), (28849422011/104857600000000), (259644798099/209715200000000), (85729066033/26214400000000), (583227942231/104857600000000), (1650524786693/262144000000000), (496333145431/104857600000000), (59654945713/26214400000000), (133023515987/209715200000000), (40924014687/524288000000000), 0]

def minusWeights0071 : Fin 11 → ℚ := ![(28849422011/1048576000000000), (28849422011/104857600000000), (259644798099/209715200000000), (87367466033/26214400000000), (628447782231/104857600000000), (1984502386693/262144000000000), (715342579031/104857600000000), (113441586353/26214400000000), (386266080211/209715200000000), (247570205423/524288000000000), (28849422011/524288000000000)]

theorem checked0071 :
    (∀ i, 0 ≤ plusWeights0071 i) ∧
    (∀ i, 0 ≤ minusWeights0071 i) ∧
    (∀ i, plusCoefficients coefficients0071 upper0071 i = powerCoefficients10 plusWeights0071 i) ∧
    (∀ i, minusCoefficients coefficients0071 upper0071 i = powerCoefficients10 minusWeights0071 i) := by
  decide +kernel

theorem bound0071 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0071 g| ≤ (upper0071 : ℝ) :=
  abs_of_coefficients coefficients0071 upper0071 powerCoefficients10 plusWeights0071 minusWeights0071
    checked0071.1 checked0071.2.1 checked0071.2.2.1 checked0071.2.2.2
    (power_identity10 plusWeights0071) (power_identity10 minusWeights0071) g hg hmax

def envelope0071 : Envelope := ⟨coefficients0071, upper0071, bound0071⟩

def coefficients0072 : Fin 11 → ℚ := ![0, 0, 0, (-1/32), (7/128), (21/256), (427/2048), (29/256), (195/1024), (2245/16384), (9905/131072)]

def upper0072 : ℚ := (6485197299/262144000000000)

def plusWeights0072 : Fin 11 → ℚ := ![(6485197299/262144000000000), (6485197299/26214400000000), (58366775691/52428800000000), (19250791897/6553600000000), (130598103279/26214400000000), (367763589837/65536000000000), (109780528879/26214400000000), (13063691737/6553600000000), (28758724491/52428800000000), (1741334011/26214400000000), 0]

def minusWeights0072 : Fin 11 → ℚ := ![(6485197299/262144000000000), (6485197299/26214400000000), (58366775691/52428800000000), (19660391897/6553600000000), (141780183279/26214400000000), (449371269837/65536000000000), (162597757679/26214400000000), (25847492057/6553600000000), (87974826891/52428800000000), (11229060587/26214400000000), (6485197299/131072000000000)]

theorem checked0072 :
    (∀ i, 0 ≤ plusWeights0072 i) ∧
    (∀ i, 0 ≤ minusWeights0072 i) ∧
    (∀ i, plusCoefficients coefficients0072 upper0072 i = powerCoefficients10 plusWeights0072 i) ∧
    (∀ i, minusCoefficients coefficients0072 upper0072 i = powerCoefficients10 minusWeights0072 i) := by
  decide +kernel

theorem bound0072 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0072 g| ≤ (upper0072 : ℝ) :=
  abs_of_coefficients coefficients0072 upper0072 powerCoefficients10 plusWeights0072 minusWeights0072
    checked0072.1 checked0072.2.1 checked0072.2.2.1 checked0072.2.2.2
    (power_identity10 plusWeights0072) (power_identity10 minusWeights0072) g hg hmax

def envelope0072 : Envelope := ⟨coefficients0072, upper0072, bound0072⟩

def coefficients0073 : Fin 11 → ℚ := ![0, 0, 0, (-1/32), (7/128), (47/512), (499/2048), (565/4096), (3297/16384), (4679/32768), (1045/16384)]

def upper0073 : ℚ := (201553293/8192000000000)

def plusWeights0073 : Fin 11 → ℚ := ![(201553293/8192000000000), (201553293/819200000000), (1813979637/1638400000000), (598259879/204800000000), (4057899153/819200000000), (11422937459/2048000000000), (3407778753/819200000000), (12660697/6400000000), (445342967/819200000000), (2153160279/32768000000000), 0]

def minusWeights0073 : Fin 11 → ℚ := ![(201553293/8192000000000), (201553293/819200000000), (1813979637/1638400000000), (611059879/204800000000), (4407339153/819200000000), (13972777459/2048000000000), (5057459553/819200000000), (402088727/102400000000), (136863667/81920000000), (13971103161/32768000000000), (201553293/4096000000000)]

theorem checked0073 :
    (∀ i, 0 ≤ plusWeights0073 i) ∧
    (∀ i, 0 ≤ minusWeights0073 i) ∧
    (∀ i, plusCoefficients coefficients0073 upper0073 i = powerCoefficients10 plusWeights0073 i) ∧
    (∀ i, minusCoefficients coefficients0073 upper0073 i = powerCoefficients10 minusWeights0073 i) := by
  decide +kernel

theorem bound0073 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0073 g| ≤ (upper0073 : ℝ) :=
  abs_of_coefficients coefficients0073 upper0073 powerCoefficients10 plusWeights0073 minusWeights0073
    checked0073.1 checked0073.2.1 checked0073.2.2.1 checked0073.2.2.2
    (power_identity10 plusWeights0073) (power_identity10 minusWeights0073) g hg hmax

def envelope0073 : Envelope := ⟨coefficients0073, upper0073, bound0073⟩

def coefficients0074 : Fin 11 → ℚ := ![0, 0, 0, (-1/32), (7/128), (13/128), (223/1024), (1127/8192), (4613/32768), (5661/65536), (7305/262144)]

def upper0074 : ℚ := (12862146371/524288000000000)

def plusWeights0074 : Fin 11 → ℚ := ![(12862146371/524288000000000), (12862146371/52428800000000), (115759317339/104857600000000), (38176839113/13107200000000), (258922993791/52428800000000), (728733141373/131072000000000), (217339531391/52428800000000), (25828757033/13107200000000), (11350912767/20971520000000), (17139463779/262144000000000), 0]

def minusWeights0074 : Fin 11 → ℚ := ![(12862146371/524288000000000), (12862146371/52428800000000), (115759317339/104857600000000), (38996039113/13107200000000), (281287153791/52428800000000), (891897301373/131072000000000), (322870616191/52428800000000), (51344121193/13107200000000), (174764070843/104857600000000), (111481999931/262144000000000), (12862146371/262144000000000)]

theorem checked0074 :
    (∀ i, 0 ≤ plusWeights0074 i) ∧
    (∀ i, 0 ≤ minusWeights0074 i) ∧
    (∀ i, plusCoefficients coefficients0074 upper0074 i = powerCoefficients10 plusWeights0074 i) ∧
    (∀ i, minusCoefficients coefficients0074 upper0074 i = powerCoefficients10 minusWeights0074 i) := by
  decide +kernel

theorem bound0074 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0074 g| ≤ (upper0074 : ℝ) :=
  abs_of_coefficients coefficients0074 upper0074 powerCoefficients10 plusWeights0074 minusWeights0074
    checked0074.1 checked0074.2.1 checked0074.2.2.1 checked0074.2.2.2
    (power_identity10 plusWeights0074) (power_identity10 minusWeights0074) g hg hmax

def envelope0074 : Envelope := ⟨coefficients0074, upper0074, bound0074⟩

def coefficients0075 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/16), (-35/128), (-57/256), (-263/1024), (-39/256), (-337/2048), (-249/4096)]

def upper0075 : ℚ := (378241389/40960000000000)

def plusWeights0075 : Fin 11 → ℚ := ![(378241389/40960000000000), (378241389/4096000000000), (3404172501/8192000000000), (1134724167/1024000000000), (7917469169/4096000000000), (23417207507/10240000000000), (7502157169/4096000000000), (977785867/1024000000000), (2400584821/8192000000000), (32932927/819200000000), 0]

def minusWeights0075 : Fin 11 → ℚ := ![(378241389/40960000000000), (378241389/4096000000000), (3404172501/8192000000000), (1134724167/1024000000000), (7968669169/4096000000000), (24241207507/10240000000000), (8383981169/4096000000000), (1291662467/1024000000000), (4407760181/8192000000000), (591818143/4096000000000), (378241389/20480000000000)]

theorem checked0075 :
    (∀ i, 0 ≤ plusWeights0075 i) ∧
    (∀ i, 0 ≤ minusWeights0075 i) ∧
    (∀ i, plusCoefficients coefficients0075 upper0075 i = powerCoefficients10 plusWeights0075 i) ∧
    (∀ i, minusCoefficients coefficients0075 upper0075 i = powerCoefficients10 minusWeights0075 i) := by
  decide +kernel

theorem bound0075 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0075 g| ≤ (upper0075 : ℝ) :=
  abs_of_coefficients coefficients0075 upper0075 powerCoefficients10 plusWeights0075 minusWeights0075
    checked0075.1 checked0075.2.1 checked0075.2.2.1 checked0075.2.2.2
    (power_identity10 plusWeights0075) (power_identity10 minusWeights0075) g hg hmax

def envelope0075 : Envelope := ⟨coefficients0075, upper0075, bound0075⟩

def coefficients0076 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/16), (-35/128), (-109/512), (-931/4096), (-295/2048), (-2913/16384), (-2251/32768)]

def upper0076 : ℚ := (3021740511/327680000000000)

def plusWeights0076 : Fin 11 → ℚ := ![(3021740511/327680000000000), (3021740511/32768000000000), (27195664599/65536000000000), (9065221533/8192000000000), (63251750731/32768000000000), (187073652193/81920000000000), (59929574731/32768000000000), (7810059333/8192000000000), (19171389399/65536000000000), (262940377/6553600000000), 0]

def minusWeights0076 : Fin 11 → ℚ := ![(3021740511/327680000000000), (3021740511/32768000000000), (27195664599/65536000000000), (9065221533/8192000000000), (63661350731/32768000000000), (193665652193/81920000000000), (66983526731/32768000000000), (10320383733/8192000000000), (35219939799/65536000000000), (4728779137/32768000000000), (3021740511/163840000000000)]

theorem checked0076 :
    (∀ i, 0 ≤ plusWeights0076 i) ∧
    (∀ i, 0 ≤ minusWeights0076 i) ∧
    (∀ i, plusCoefficients coefficients0076 upper0076 i = powerCoefficients10 plusWeights0076 i) ∧
    (∀ i, minusCoefficients coefficients0076 upper0076 i = powerCoefficients10 minusWeights0076 i) := by
  decide +kernel

theorem bound0076 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0076 g| ≤ (upper0076 : ℝ) :=
  abs_of_coefficients coefficients0076 upper0076 powerCoefficients10 plusWeights0076 minusWeights0076
    checked0076.1 checked0076.2.1 checked0076.2.2.1 checked0076.2.2.2
    (power_identity10 plusWeights0076) (power_identity10 minusWeights0076) g hg hmax

def envelope0076 : Envelope := ⟨coefficients0076, upper0076, bound0076⟩

def coefficients0077 : Fin 11 → ℚ := ![0, 0, 0, 0, (-3/64), (-45/256), (-151/1024), (-1151/8192), (-369/4096), (-2323/32768), (-1481/65536)]

def upper0077 : ℚ := (4330486341/655360000000000)

def plusWeights0077 : Fin 11 → ℚ := ![(4330486341/655360000000000), (4330486341/65536000000000), (38974377069/131072000000000), (12991459023/16384000000000), (90633013161/65536000000000), (267924639483/163840000000000), (85746549161/65536000000000), (11157564823/16384000000000), (27332766189/131072000000000), (373949043/13107200000000), 0]

def minusWeights0077 : Fin 11 → ℚ := ![(4330486341/655360000000000), (4330486341/65536000000000), (38974377069/131072000000000), (12991459023/16384000000000), (91247413161/65536000000000), (277716639483/163840000000000), (96133877161/65536000000000), (14825353223/16384000000000), (50615987949/131072000000000), (6791227467/65536000000000), (4330486341/327680000000000)]

theorem checked0077 :
    (∀ i, 0 ≤ plusWeights0077 i) ∧
    (∀ i, 0 ≤ minusWeights0077 i) ∧
    (∀ i, plusCoefficients coefficients0077 upper0077 i = powerCoefficients10 plusWeights0077 i) ∧
    (∀ i, minusCoefficients coefficients0077 upper0077 i = powerCoefficients10 minusWeights0077 i) := by
  decide +kernel

theorem bound0077 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0077 g| ≤ (upper0077 : ℝ) :=
  abs_of_coefficients coefficients0077 upper0077 powerCoefficients10 plusWeights0077 minusWeights0077
    checked0077.1 checked0077.2.1 checked0077.2.2.1 checked0077.2.2.2
    (power_identity10 plusWeights0077) (power_identity10 minusWeights0077) g hg hmax

def envelope0077 : Envelope := ⟨coefficients0077, upper0077, bound0077⟩

def coefficients0078 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/32), (-25/128), (-67/512), (-431/4096), (-81/2048), (-1123/16384), (-921/32768)]

def upper0078 : ℚ := (1710480981/327680000000000)

def plusWeights0078 : Fin 11 → ℚ := ![(1710480981/327680000000000), (1710480981/32768000000000), (15394328829/65536000000000), (5131442943/8192000000000), (35817700601/32768000000000), (106064301803/81920000000000), (34059812601/32768000000000), (4455068743/8192000000000), (10988778109/65536000000000), (151573283/6553600000000), 0]

def minusWeights0078 : Fin 11 → ℚ := ![(1710480981/327680000000000), (1710480981/32768000000000), (15394328829/65536000000000), (5131442943/8192000000000), (36022500601/32768000000000), (109456301803/81920000000000), (37780388601/32768000000000), (5807817143/8192000000000), (19799879549/65536000000000), (2663095547/32768000000000), (1710480981/163840000000000)]

theorem checked0078 :
    (∀ i, 0 ≤ plusWeights0078 i) ∧
    (∀ i, 0 ≤ minusWeights0078 i) ∧
    (∀ i, plusCoefficients coefficients0078 upper0078 i = powerCoefficients10 plusWeights0078 i) ∧
    (∀ i, minusCoefficients coefficients0078 upper0078 i = powerCoefficients10 minusWeights0078 i) := by
  decide +kernel

theorem bound0078 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0078 g| ≤ (upper0078 : ℝ) :=
  abs_of_coefficients coefficients0078 upper0078 powerCoefficients10 plusWeights0078 minusWeights0078
    checked0078.1 checked0078.2.1 checked0078.2.2.1 checked0078.2.2.2
    (power_identity10 plusWeights0078) (power_identity10 minusWeights0078) g hg hmax

def envelope0078 : Envelope := ⟨coefficients0078, upper0078, bound0078⟩

def coefficients0079 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/32), (-11/64), (-53/512), (-25/256), (-107/2048), (-1345/16384), (-1115/32768)]

def upper0079 : ℚ := (324903843/65536000000000)

def plusWeights0079 : Fin 11 → ℚ := ![(324903843/65536000000000), (324903843/6553600000000), (2924134587/13107200000000), (974711529/1638400000000), (6802500703/6553600000000), (20133582109/16384000000000), (6458782303/6553600000000), (843457129/1638400000000), (2075922939/13107200000000), (142790857/6553600000000), 0]

def minusWeights0079 : Fin 11 → ℚ := ![(324903843/65536000000000), (324903843/6553600000000), (2924134587/13107200000000), (974711529/1638400000000), (6843460703/6553600000000), (20804302109/16384000000000), (7187179103/6553600000000), (1105965929/1638400000000), (754469247/2621440000000), (507016829/6553600000000), (324903843/32768000000000)]

theorem checked0079 :
    (∀ i, 0 ≤ plusWeights0079 i) ∧
    (∀ i, 0 ≤ minusWeights0079 i) ∧
    (∀ i, plusCoefficients coefficients0079 upper0079 i = powerCoefficients10 plusWeights0079 i) ∧
    (∀ i, minusCoefficients coefficients0079 upper0079 i = powerCoefficients10 minusWeights0079 i) := by
  decide +kernel

theorem bound0079 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0079 g| ≤ (upper0079 : ℝ) :=
  abs_of_coefficients coefficients0079 upper0079 powerCoefficients10 plusWeights0079 minusWeights0079
    checked0079.1 checked0079.2.1 checked0079.2.2.1 checked0079.2.2.2
    (power_identity10 plusWeights0079) (power_identity10 minusWeights0079) g hg hmax

def envelope0079 : Envelope := ⟨coefficients0079, upper0079, bound0079⟩

def coefficients0080 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/32), (-35/256), (-57/512), (-875/8192), (-253/4096), (-2005/32768), (-1435/65536)]

def upper0080 : ℚ := (604881267/131072000000000)

def plusWeights0080 : Fin 11 → ℚ := ![(604881267/131072000000000), (604881267/13107200000000), (5443931403/26214400000000), (1814643801/3276800000000), (12661546607/13107200000000), (37448319821/32768000000000), (11997047407/13107200000000), (1563549601/3276800000000), (3838364811/26214400000000), (263247473/13107200000000), 0]

def minusWeights0080 : Fin 11 → ℚ := ![(604881267/131072000000000), (604881267/13107200000000), (5443931403/26214400000000), (1814643801/3276800000000), (12743466607/13107200000000), (38766719821/32768000000000), (13407965807/13107200000000), (2065738001/3276800000000), (1409899599/5242880000000), (946515061/13107200000000), (604881267/65536000000000)]

theorem checked0080 :
    (∀ i, 0 ≤ plusWeights0080 i) ∧
    (∀ i, 0 ≤ minusWeights0080 i) ∧
    (∀ i, plusCoefficients coefficients0080 upper0080 i = powerCoefficients10 plusWeights0080 i) ∧
    (∀ i, minusCoefficients coefficients0080 upper0080 i = powerCoefficients10 minusWeights0080 i) := by
  decide +kernel

theorem bound0080 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0080 g| ≤ (upper0080 : ℝ) :=
  abs_of_coefficients coefficients0080 upper0080 powerCoefficients10 plusWeights0080 minusWeights0080
    checked0080.1 checked0080.2.1 checked0080.2.2.1 checked0080.2.2.2
    (power_identity10 plusWeights0080) (power_identity10 minusWeights0080) g hg hmax

def envelope0080 : Envelope := ⟨coefficients0080, upper0080, bound0080⟩

def coefficients0081 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/32), (-29/256), (-19/256), (-265/4096), (-77/2048), (-115/4096), (-145/16384)]

def upper0081 : ℚ := (142177269/32768000000000)

def plusWeights0081 : Fin 11 → ℚ := ![(142177269/32768000000000), (142177269/3276800000000), (1279595421/6553600000000), (426531807/819200000000), (2975482649/3276800000000), (8794287947/8192000000000), (2813319449/3276800000000), (365803307/819200000000), (895107357/6553600000000), (61138313/3276800000000), 0]

def minusWeights0081 : Fin 11 → ℚ := ![(142177269/32768000000000), (142177269/3276800000000), (1279595421/6553600000000), (426531807/819200000000), (2995962649/3276800000000), (9120047947/8192000000000), (3158125849/3276800000000), (487260307/819200000000), (332816697/1310720000000), (8928649/131072000000), (142177269/16384000000000)]

theorem checked0081 :
    (∀ i, 0 ≤ plusWeights0081 i) ∧
    (∀ i, 0 ≤ minusWeights0081 i) ∧
    (∀ i, plusCoefficients coefficients0081 upper0081 i = powerCoefficients10 plusWeights0081 i) ∧
    (∀ i, minusCoefficients coefficients0081 upper0081 i = powerCoefficients10 minusWeights0081 i) := by
  decide +kernel

theorem bound0081 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0081 g| ≤ (upper0081 : ℝ) :=
  abs_of_coefficients coefficients0081 upper0081 powerCoefficients10 plusWeights0081 minusWeights0081
    checked0081.1 checked0081.2.1 checked0081.2.2.1 checked0081.2.2.2
    (power_identity10 plusWeights0081) (power_identity10 minusWeights0081) g hg hmax

def envelope0081 : Envelope := ⟨coefficients0081, upper0081, bound0081⟩

def coefficients0082 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/64), (-25/256), (-9/128), (-179/2048), (-11/256), (-669/16384), (-473/32768)]

def upper0082 : ℚ := (858058653/327680000000000)

def plusWeights0082 : Fin 11 → ℚ := ![(858058653/327680000000000), (858058653/32768000000000), (7722527877/65536000000000), (2574175959/8192000000000), (17968031713/32768000000000), (53209695139/81920000000000), (17088927713/32768000000000), (2235800359/8192000000000), (5517133317/65536000000000), (76150791/6553600000000), 0]

def minusWeights0082 : Fin 11 → ℚ := ![(858058653/327680000000000), (858058653/32768000000000), (7722527877/65536000000000), (2574175959/8192000000000), (18070431713/32768000000000), (54905695139/81920000000000), (18949535713/32768000000000), (2912551559/8192000000000), (9927922437/65536000000000), (1335363351/32768000000000), (858058653/163840000000000)]

theorem checked0082 :
    (∀ i, 0 ≤ plusWeights0082 i) ∧
    (∀ i, 0 ≤ minusWeights0082 i) ∧
    (∀ i, plusCoefficients coefficients0082 upper0082 i = powerCoefficients10 plusWeights0082 i) ∧
    (∀ i, minusCoefficients coefficients0082 upper0082 i = powerCoefficients10 minusWeights0082 i) := by
  decide +kernel

theorem bound0082 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0082 g| ≤ (upper0082 : ℝ) :=
  abs_of_coefficients coefficients0082 upper0082 powerCoefficients10 plusWeights0082 minusWeights0082
    checked0082.1 checked0082.2.1 checked0082.2.2.1 checked0082.2.2.2
    (power_identity10 plusWeights0082) (power_identity10 minusWeights0082) g hg hmax

def envelope0082 : Envelope := ⟨coefficients0082, upper0082, bound0082⟩

def coefficients0083 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/64), (-25/256), (-67/1024), (-431/8192), (-81/4096), (-423/32768), (-221/65536)]

def upper0083 : ℚ := (1710466281/655360000000000)

def plusWeights0083 : Fin 11 → ℚ := ![(1710466281/655360000000000), (1710466281/65536000000000), (15394196529/131072000000000), (5131398843/16384000000000), (35817391901/65536000000000), (106063375703/163840000000000), (34059503901/65536000000000), (4455024643/16384000000000), (10988645809/131072000000000), (151570623/13107200000000), 0]

def minusWeights0083 : Fin 11 → ℚ := ![(1710466281/655360000000000), (1710466281/65536000000000), (15394196529/131072000000000), (5131398843/16384000000000), (36022191901/65536000000000), (109455375703/163840000000000), (37780079901/65536000000000), (5807773043/16384000000000), (19799747249/131072000000000), (2663079447/65536000000000), (1710466281/327680000000000)]

theorem checked0083 :
    (∀ i, 0 ≤ plusWeights0083 i) ∧
    (∀ i, 0 ≤ minusWeights0083 i) ∧
    (∀ i, plusCoefficients coefficients0083 upper0083 i = powerCoefficients10 plusWeights0083 i) ∧
    (∀ i, minusCoefficients coefficients0083 upper0083 i = powerCoefficients10 minusWeights0083 i) := by
  decide +kernel

theorem bound0083 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0083 g| ≤ (upper0083 : ℝ) :=
  abs_of_coefficients coefficients0083 upper0083 powerCoefficients10 plusWeights0083 minusWeights0083
    checked0083.1 checked0083.2.1 checked0083.2.2.1 checked0083.2.2.2
    (power_identity10 plusWeights0083) (power_identity10 minusWeights0083) g hg hmax

def envelope0083 : Envelope := ⟨coefficients0083, upper0083, bound0083⟩

def coefficients0084 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/64), (-15/256), (-13/256), (-445/8192), (-149/4096), (-685/32768), (-355/65536)]

def upper0084 : ℚ := (289018491/131072000000000)

def plusWeights0084 : Fin 11 → ℚ := ![(289018491/131072000000000), (289018491/13107200000000), (2601166419/26214400000000), (867055473/3276800000000), (6048908311/13107200000000), (17881764933/32768000000000), (5723122711/13107200000000), (744772073/3276800000000), (1824742483/26214400000000), (124852681/13107200000000), 0]

def minusWeights0084 : Fin 11 → ℚ := ![(289018491/131072000000000), (289018491/13107200000000), (2601166419/26214400000000), (867055473/3276800000000), (6089868311/13107200000000), (18534564933/32768000000000), (6415653911/13107200000000), (989338873/3276800000000), (675518071/5242880000000), (453184301/13107200000000), (289018491/65536000000000)]

theorem checked0084 :
    (∀ i, 0 ≤ plusWeights0084 i) ∧
    (∀ i, 0 ≤ minusWeights0084 i) ∧
    (∀ i, plusCoefficients coefficients0084 upper0084 i = powerCoefficients10 plusWeights0084 i) ∧
    (∀ i, minusCoefficients coefficients0084 upper0084 i = powerCoefficients10 minusWeights0084 i) := by
  decide +kernel

theorem bound0084 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0084 g| ≤ (upper0084 : ℝ) :=
  abs_of_coefficients coefficients0084 upper0084 powerCoefficients10 plusWeights0084 minusWeights0084
    checked0084.1 checked0084.2.1 checked0084.2.2.1 checked0084.2.2.2
    (power_identity10 plusWeights0084) (power_identity10 minusWeights0084) g hg hmax

def envelope0084 : Envelope := ⟨coefficients0084, upper0084, bound0084⟩

def coefficients0085 : Fin 11 → ℚ := ![0, 0, 0, 0, (-1/64), (-3/64), (-33/1024), (-65/2048), (-87/4096), (-95/8192), (-95/32768)]

def upper0085 : ℚ := (135454699/65536000000000)

def plusWeights0085 : Fin 11 → ℚ := ![(135454699/65536000000000), (135454699/6553600000000), (1219092291/13107200000000), (406364097/1638400000000), (2834308679/6553600000000), (8372366037/16384000000000), (2675377479/6553600000000), (347267697/1638400000000), (847790307/13107200000000), (57744639/6553600000000), 0]

def minusWeights0085 : Fin 11 → ℚ := ![(135454699/65536000000000), (135454699/6553600000000), (1219092291/13107200000000), (406364097/1638400000000), (2854788679/6553600000000), (8694926037/16384000000000), (3013719879/6553600000000), (465460497/1638400000000), (63615771/524288000000), (213164759/6553600000000), (135454699/32768000000000)]

theorem checked0085 :
    (∀ i, 0 ≤ plusWeights0085 i) ∧
    (∀ i, 0 ≤ minusWeights0085 i) ∧
    (∀ i, plusCoefficients coefficients0085 upper0085 i = powerCoefficients10 plusWeights0085 i) ∧
    (∀ i, minusCoefficients coefficients0085 upper0085 i = powerCoefficients10 minusWeights0085 i) := by
  decide +kernel

theorem bound0085 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0085 g| ≤ (upper0085 : ℝ) :=
  abs_of_coefficients coefficients0085 upper0085 powerCoefficients10 plusWeights0085 minusWeights0085
    checked0085.1 checked0085.2.1 checked0085.2.2.1 checked0085.2.2.2
    (power_identity10 plusWeights0085) (power_identity10 minusWeights0085) g hg hmax

def envelope0085 : Envelope := ⟨coefficients0085, upper0085, bound0085⟩

def coefficients0086 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-23/256), (-31/512), (-543/4096), (-121/1024), (-1039/8192), (-773/16384)]

def upper0086 : ℚ := (159507153/163840000000000)

def plusWeights0086 : Fin 11 → ℚ := ![(159507153/163840000000000), (159507153/16384000000000), (1435564377/32768000000000), (478521459/4096000000000), (3349650213/16384000000000), (10012150639/40960000000000), (3275058213/16384000000000), (440675159/4096000000000), (1127918457/32768000000000), (16249351/3276800000000), 0]

def minusWeights0086 : Fin 11 → ℚ := ![(159507153/163840000000000), (159507153/16384000000000), (1435564377/32768000000000), (478521459/4096000000000), (3349650213/16384000000000), (10085750639/40960000000000), (3424242213/16384000000000), (516367759/4096000000000), (1743210297/32768000000000), (237767551/16384000000000), (159507153/81920000000000)]

theorem checked0086 :
    (∀ i, 0 ≤ plusWeights0086 i) ∧
    (∀ i, 0 ≤ minusWeights0086 i) ∧
    (∀ i, plusCoefficients coefficients0086 upper0086 i = powerCoefficients10 plusWeights0086 i) ∧
    (∀ i, minusCoefficients coefficients0086 upper0086 i = powerCoefficients10 minusWeights0086 i) := by
  decide +kernel

theorem bound0086 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0086 g| ≤ (upper0086 : ℝ) :=
  abs_of_coefficients coefficients0086 upper0086 powerCoefficients10 plusWeights0086 minusWeights0086
    checked0086.1 checked0086.2.1 checked0086.2.2.1 checked0086.2.2.2
    (power_identity10 plusWeights0086) (power_identity10 minusWeights0086) g hg hmax

def envelope0086 : Envelope := ⟨coefficients0086, upper0086, bound0086⟩

def coefficients0087 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-17/256), (-17/512), (-337/4096), (-143/2048), (-775/8192), (-155/4096)]

def upper0087 : ℚ := (2892963/4096000000000)

def plusWeights0087 : Fin 11 → ℚ := ![(2892963/4096000000000), (2892963/409600000000), (26036667/819200000000), (8678889/102400000000), (60752223/409600000000), (181576669/1024000000000), (59378623/409600000000), (15968893/204800000000), (816507/32768000000), (5871369/1638400000000), 0]

def minusWeights0087 : Fin 11 → ℚ := ![(2892963/4096000000000), (2892963/409600000000), (26036667/819200000000), (8678889/102400000000), (60752223/409600000000), (182936669/1024000000000), (62125823/409600000000), (18746663/204800000000), (31660659/819200000000), (3454467/327680000000), (2892963/2048000000000)]

theorem checked0087 :
    (∀ i, 0 ≤ plusWeights0087 i) ∧
    (∀ i, 0 ≤ minusWeights0087 i) ∧
    (∀ i, plusCoefficients coefficients0087 upper0087 i = powerCoefficients10 plusWeights0087 i) ∧
    (∀ i, minusCoefficients coefficients0087 upper0087 i = powerCoefficients10 minusWeights0087 i) := by
  decide +kernel

theorem bound0087 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0087 g| ≤ (upper0087 : ℝ) :=
  abs_of_coefficients coefficients0087 upper0087 powerCoefficients10 plusWeights0087 minusWeights0087
    checked0087.1 checked0087.2.1 checked0087.2.2.1 checked0087.2.2.2
    (power_identity10 plusWeights0087) (power_identity10 minusWeights0087) g hg hmax

def envelope0087 : Envelope := ⟨coefficients0087, upper0087, bound0087⟩

def coefficients0088 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/16), (17/128), (-1/1024), (1535/4096), (1455/8192), (3775/32768)]

def upper0088 : ℚ := (6400881/13107200000000)

def plusWeights0088 : Fin 11 → ℚ := ![(6400881/13107200000000), (6400881/1310720000000), (57607929/2621440000000), (19202643/327680000000), (134418501/1310720000000), (401207503/3276800000000), (130496581/1310720000000), (17328691/327680000000), (8664389/524288000000), (15054369/6553600000000), 0]

def minusWeights0088 : Fin 11 → ℚ := ![(6400881/13107200000000), (6400881/1310720000000), (57607929/2621440000000), (19202643/327680000000), (134418501/1310720000000), (405303503/3276800000000), (138340421/1310720000000), (4215319/65536000000), (71893913/2621440000000), (48954441/6553600000000), (6400881/6553600000000)]

theorem checked0088 :
    (∀ i, 0 ≤ plusWeights0088 i) ∧
    (∀ i, 0 ≤ minusWeights0088 i) ∧
    (∀ i, plusCoefficients coefficients0088 upper0088 i = powerCoefficients10 plusWeights0088 i) ∧
    (∀ i, minusCoefficients coefficients0088 upper0088 i = powerCoefficients10 minusWeights0088 i) := by
  decide +kernel

theorem bound0088 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0088 g| ≤ (upper0088 : ℝ) :=
  abs_of_coefficients coefficients0088 upper0088 powerCoefficients10 plusWeights0088 minusWeights0088
    checked0088.1 checked0088.2.1 checked0088.2.2.1 checked0088.2.2.2
    (power_identity10 plusWeights0088) (power_identity10 minusWeights0088) g hg hmax

def envelope0088 : Envelope := ⟨coefficients0088, upper0088, bound0088⟩

def coefficients0089 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/16), (17/128), (-1/1024), (1585/4096), (1405/8192), (5275/65536)]

def upper0089 : ℚ := (12798813/26214400000000)

def plusWeights0089 : Fin 11 → ℚ := ![(12798813/26214400000000), (12798813/2621440000000), (115189317/5242880000000), (38396439/655360000000), (268775073/2621440000000), (802229219/6553600000000), (260931233/2621440000000), (6929707/131072000000), (86617989/5242880000000), (30097113/13107200000000), 0]

def minusWeights0089 : Fin 11 → ℚ := ![(12798813/26214400000000), (12798813/2621440000000), (115189317/5242880000000), (38396439/655360000000), (268775073/2621440000000), (810421219/6553600000000), (276618913/2621440000000), (42144343/655360000000), (28752129/1048576000000), (97891017/13107200000000), (12798813/13107200000000)]

theorem checked0089 :
    (∀ i, 0 ≤ plusWeights0089 i) ∧
    (∀ i, 0 ≤ minusWeights0089 i) ∧
    (∀ i, plusCoefficients coefficients0089 upper0089 i = powerCoefficients10 plusWeights0089 i) ∧
    (∀ i, minusCoefficients coefficients0089 upper0089 i = powerCoefficients10 minusWeights0089 i) := by
  decide +kernel

theorem bound0089 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0089 g| ≤ (upper0089 : ℝ) :=
  abs_of_coefficients coefficients0089 upper0089 powerCoefficients10 plusWeights0089 minusWeights0089
    checked0089.1 checked0089.2.1 checked0089.2.2.1 checked0089.2.2.2
    (power_identity10 plusWeights0089) (power_identity10 minusWeights0089) g hg hmax

def envelope0089 : Envelope := ⟨coefficients0089, upper0089, bound0089⟩

def coefficients0090 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/256), (-15/512), (-275/8192), (-25/4096), (-225/32768), (-175/65536)]

def upper0090 : ℚ := (16217787/26214400000000)

def plusWeights0090 : Fin 11 → ℚ := ![(16217787/26214400000000), (16217787/2621440000000), (145960083/5242880000000), (48653361/655360000000), (340573527/2621440000000), (1017880581/6553600000000), (332816727/2621440000000), (44734361/655360000000), (114265363/5242880000000), (8203849/2621440000000), 0]

def minusWeights0090 : Fin 11 → ℚ := ![(16217787/26214400000000), (16217787/2621440000000), (145960083/5242880000000), (48653361/655360000000), (340573527/2621440000000), (1025560581/6553600000000), (348330327/2621440000000), (52572361/655360000000), (177654803/5242880000000), (969269/104857600000), (16217787/13107200000000)]

theorem checked0090 :
    (∀ i, 0 ≤ plusWeights0090 i) ∧
    (∀ i, 0 ≤ minusWeights0090 i) ∧
    (∀ i, plusCoefficients coefficients0090 upper0090 i = powerCoefficients10 plusWeights0090 i) ∧
    (∀ i, minusCoefficients coefficients0090 upper0090 i = powerCoefficients10 minusWeights0090 i) := by
  decide +kernel

theorem bound0090 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0090 g| ≤ (upper0090 : ℝ) :=
  abs_of_coefficients coefficients0090 upper0090 powerCoefficients10 plusWeights0090 minusWeights0090
    checked0090.1 checked0090.2.1 checked0090.2.2.1 checked0090.2.2.2
    (power_identity10 plusWeights0090) (power_identity10 minusWeights0090) g hg hmax

def envelope0090 : Envelope := ⟨coefficients0090, upper0090, bound0090⟩

def coefficients0091 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/256), (3/256), (117/4096), (1149/16384), (993/32768), (3615/262144)]

def upper0091 : ℚ := (299174109/524288000000000)

def plusWeights0091 : Fin 11 → ℚ := ![(299174109/524288000000000), (299174109/52428800000000), (2692566981/104857600000000), (897522327/13107200000000), (6282656289/52428800000000), (18771168867/131072000000000), (6129670689/52428800000000), (821374167/13107200000000), (2086511877/104857600000000), (742780569/262144000000000), 0]

def minusWeights0091 : Fin 11 → ℚ := ![(299174109/524288000000000), (299174109/52428800000000), (2692566981/104857600000000), (897522327/13107200000000), (6282656289/52428800000000), (18924768867/131072000000000), (6435641889/52428800000000), (973670487/13107200000000), (659724417/20971520000000), (2248960521/262144000000000), (299174109/262144000000000)]

theorem checked0091 :
    (∀ i, 0 ≤ plusWeights0091 i) ∧
    (∀ i, 0 ≤ minusWeights0091 i) ∧
    (∀ i, plusCoefficients coefficients0091 upper0091 i = powerCoefficients10 plusWeights0091 i) ∧
    (∀ i, minusCoefficients coefficients0091 upper0091 i = powerCoefficients10 minusWeights0091 i) := by
  decide +kernel

theorem bound0091 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0091 g| ≤ (upper0091 : ℝ) :=
  abs_of_coefficients coefficients0091 upper0091 powerCoefficients10 plusWeights0091 minusWeights0091
    checked0091.1 checked0091.2.1 checked0091.2.2.1 checked0091.2.2.2
    (power_identity10 plusWeights0091) (power_identity10 minusWeights0091) g hg hmax

def envelope0091 : Envelope := ⟨coefficients0091, upper0091, bound0091⟩

def coefficients0092 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/256), (93/2048), (9/256), (4341/32768), (4737/65536), (23295/262144)]

def upper0092 : ℚ := (56162337/104857600000000)

def plusWeights0092 : Fin 11 → ℚ := ![(56162337/104857600000000), (56162337/10485760000000), (505461033/20971520000000), (168487011/2621440000000), (1179409077/10485760000000), (3522867231/26214400000000), (1149165237/10485760000000), (153612387/2621440000000), (1942719597/104857600000000), (687152733/262144000000000), 0]

def minusWeights0092 : Fin 11 → ℚ := ![(56162337/104857600000000), (56162337/10485760000000), (505461033/20971520000000), (168487011/2621440000000), (1179409077/10485760000000), (3553587231/26214400000000), (1209652917/10485760000000), (36672327/524288000000), (3111890733/104857600000000), (2120964117/262144000000000), (56162337/52428800000000)]

theorem checked0092 :
    (∀ i, 0 ≤ plusWeights0092 i) ∧
    (∀ i, 0 ≤ minusWeights0092 i) ∧
    (∀ i, plusCoefficients coefficients0092 upper0092 i = powerCoefficients10 plusWeights0092 i) ∧
    (∀ i, minusCoefficients coefficients0092 upper0092 i = powerCoefficients10 minusWeights0092 i) := by
  decide +kernel

theorem bound0092 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0092 g| ≤ (upper0092 : ℝ) :=
  abs_of_coefficients coefficients0092 upper0092 powerCoefficients10 plusWeights0092 minusWeights0092
    checked0092.1 checked0092.2.1 checked0092.2.2.1 checked0092.2.2.2
    (power_identity10 plusWeights0092) (power_identity10 minusWeights0092) g hg hmax

def envelope0092 : Envelope := ⟨coefficients0092, upper0092, bound0092⟩

def coefficients0093 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-25/512), (-29/1024), (-351/4096), (-157/2048), (-1365/16384), (-1005/32768)]

def upper0093 : ℚ := (34473501/65536000000000)

def plusWeights0093 : Fin 11 → ℚ := ![(34473501/65536000000000), (34473501/6553600000000), (310261509/13107200000000), (103420503/1638400000000), (723943521/6553600000000), (2163830563/16384000000000), (707757921/6553600000000), (95220863/1638400000000), (243687301/13107200000000), (17552027/6553600000000), 0]

def minusWeights0093 : Fin 11 → ℚ := ![(34473501/65536000000000), (34473501/6553600000000), (310261509/13107200000000), (103420503/1638400000000), (723943521/6553600000000), (2179830563/16384000000000), (740129121/6553600000000), (111620143/1638400000000), (376835717/13107200000000), (2055799/262144000000), (34473501/32768000000000)]

theorem checked0093 :
    (∀ i, 0 ≤ plusWeights0093 i) ∧
    (∀ i, 0 ≤ minusWeights0093 i) ∧
    (∀ i, plusCoefficients coefficients0093 upper0093 i = powerCoefficients10 plusWeights0093 i) ∧
    (∀ i, minusCoefficients coefficients0093 upper0093 i = powerCoefficients10 minusWeights0093 i) := by
  decide +kernel

theorem bound0093 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0093 g| ≤ (upper0093 : ℝ) :=
  abs_of_coefficients coefficients0093 upper0093 powerCoefficients10 plusWeights0093 minusWeights0093
    checked0093.1 checked0093.2.1 checked0093.2.2.1 checked0093.2.2.2
    (power_identity10 plusWeights0093) (power_identity10 minusWeights0093) g hg hmax

def envelope0093 : Envelope := ⟨coefficients0093, upper0093, bound0093⟩

def coefficients0094 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/64), (-29/256), (-507/2048), (-111/1024), (-913/4096), (-393/4096)]

def upper0094 : ℚ := (24907923/40960000000000)

def plusWeights0094 : Fin 11 → ℚ := ![(24907923/40960000000000), (24907923/4096000000000), (224171307/8192000000000), (74723769/1024000000000), (523066383/4096000000000), (1564399149/10240000000000), (513002383/4096000000000), (69434419/1024000000000), (179586027/8192000000000), (1313793/409600000000), 0]

def minusWeights0094 : Fin 11 → ℚ := ![(24907923/40960000000000), (24907923/4096000000000), (224171307/8192000000000), (74723769/1024000000000), (523066383/4096000000000), (1573999149/10240000000000), (533130383/4096000000000), (80013119/1024000000000), (268756587/8192000000000), (9169479/1024000000000), (24907923/20480000000000)]

theorem checked0094 :
    (∀ i, 0 ≤ plusWeights0094 i) ∧
    (∀ i, 0 ≤ minusWeights0094 i) ∧
    (∀ i, plusCoefficients coefficients0094 upper0094 i = powerCoefficients10 plusWeights0094 i) ∧
    (∀ i, minusCoefficients coefficients0094 upper0094 i = powerCoefficients10 minusWeights0094 i) := by
  decide +kernel

theorem bound0094 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0094 g| ≤ (upper0094 : ℝ) :=
  abs_of_coefficients coefficients0094 upper0094 powerCoefficients10 plusWeights0094 minusWeights0094
    checked0094.1 checked0094.2.1 checked0094.2.2.1 checked0094.2.2.2
    (power_identity10 plusWeights0094) (power_identity10 minusWeights0094) g hg hmax

def envelope0094 : Envelope := ⟨coefficients0094, upper0094, bound0094⟩

def coefficients0095 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/64), (-29/256), (-921/4096), (-37/256), (-6571/32768), (-5227/65536)]

def upper0095 : ℚ := (397259847/655360000000000)

def plusWeights0095 : Fin 11 → ℚ := ![(397259847/655360000000000), (397259847/65536000000000), (3575338623/131072000000000), (1191779541/16384000000000), (8342456787/65536000000000), (24950570361/163840000000000), (8181432787/65536000000000), (1107187141/16384000000000), (2862819583/131072000000000), (41868093/13107200000000), 0]

def minusWeights0095 : Fin 11 → ℚ := ![(397259847/655360000000000), (397259847/65536000000000), (3575338623/131072000000000), (1191779541/16384000000000), (8342456787/65536000000000), (25104170361/163840000000000), (8503480787/65536000000000), (1276371941/16384000000000), (4287857663/131072000000000), (585179229/65536000000000), (397259847/327680000000000)]

theorem checked0095 :
    (∀ i, 0 ≤ plusWeights0095 i) ∧
    (∀ i, 0 ≤ minusWeights0095 i) ∧
    (∀ i, plusCoefficients coefficients0095 upper0095 i = powerCoefficients10 plusWeights0095 i) ∧
    (∀ i, minusCoefficients coefficients0095 upper0095 i = powerCoefficients10 minusWeights0095 i) := by
  decide +kernel

theorem bound0095 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0095 g| ≤ (upper0095 : ℝ) :=
  abs_of_coefficients coefficients0095 upper0095 powerCoefficients10 plusWeights0095 minusWeights0095
    checked0095.1 checked0095.2.1 checked0095.2.2.1 checked0095.2.2.2
    (power_identity10 plusWeights0095) (power_identity10 minusWeights0095) g hg hmax

def envelope0095 : Envelope := ⟨coefficients0095, upper0095, bound0095⟩

end BilayerDressed.CubicQuarticEnvelopes

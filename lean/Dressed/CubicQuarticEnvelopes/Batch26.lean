import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0832 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/2048), (15/1024), (105/16384), (225/32768), (75/524288)]

def upper0832 : ℚ := (4930083/209715200000000)

def plusWeights0832 : Fin 11 → ℚ := ![(4930083/209715200000000), (4930083/20971520000000), (44370747/41943040000000), (14790249/5242880000000), (103531743/20971520000000), (310595229/52428800000000), (103992543/20971520000000), (15258729/5242880000000), (10017471/8388608000000), (274731/838860800000), (4930083/104857600000000)]

def minusWeights0832 : Fin 11 → ℚ := ![(4930083/209715200000000), (4930083/20971520000000), (44370747/41943040000000), (14790249/5242880000000), (103531743/20971520000000), (310595229/52428800000000), (103070943/20971520000000), (14321769/5242880000000), (38654139/41943040000000), (2991891/20971520000000), 0]

theorem checked0832 :
    (∀ i, 0 ≤ plusWeights0832 i) ∧
    (∀ i, 0 ≤ minusWeights0832 i) ∧
    (∀ i, plusCoefficients coefficients0832 upper0832 i = powerCoefficients10 plusWeights0832 i) ∧
    (∀ i, minusCoefficients coefficients0832 upper0832 i = powerCoefficients10 minusWeights0832 i) := by
  decide +kernel

theorem bound0832 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0832 g| ≤ (upper0832 : ℝ) :=
  abs_of_coefficients coefficients0832 upper0832 powerCoefficients10 plusWeights0832 minusWeights0832
    checked0832.1 checked0832.2.1 checked0832.2.2.1 checked0832.2.2.2
    (power_identity10 plusWeights0832) (power_identity10 minusWeights0832) g hg hmax

def envelope0832 : Envelope := ⟨coefficients0832, upper0832, bound0832⟩

def coefficients0833 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/2048), (15/1024), (45/4096), (75/8192), (825/524288)]

def upper0833 : ℚ := (4940193/209715200000000)

def plusWeights0833 : Fin 11 → ℚ := ![(4940193/209715200000000), (4940193/20971520000000), (44461737/41943040000000), (14820579/5242880000000), (103744053/20971520000000), (311232159/52428800000000), (104204853/20971520000000), (15289059/5242880000000), (10036053/8388608000000), (6880353/20971520000000), (4940193/104857600000000)]

def minusWeights0833 : Fin 11 → ℚ := ![(4940193/209715200000000), (4940193/20971520000000), (44461737/41943040000000), (14820579/5242880000000), (103744053/20971520000000), (311232159/52428800000000), (103283253/20971520000000), (14352099/5242880000000), (38743209/41943040000000), (3000033/20971520000000), 0]

theorem checked0833 :
    (∀ i, 0 ≤ plusWeights0833 i) ∧
    (∀ i, 0 ≤ minusWeights0833 i) ∧
    (∀ i, plusCoefficients coefficients0833 upper0833 i = powerCoefficients10 plusWeights0833 i) ∧
    (∀ i, minusCoefficients coefficients0833 upper0833 i = powerCoefficients10 minusWeights0833 i) := by
  decide +kernel

theorem bound0833 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0833 g| ≤ (upper0833 : ℝ) :=
  abs_of_coefficients coefficients0833 upper0833 powerCoefficients10 plusWeights0833 minusWeights0833
    checked0833.1 checked0833.2.1 checked0833.2.2.1 checked0833.2.2.2
    (power_identity10 plusWeights0833) (power_identity10 minusWeights0833) g hg hmax

def envelope0833 : Envelope := ⟨coefficients0833, upper0833, bound0833⟩

def coefficients0834 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/2048), (15/1024), (615/32768), (1035/65536), (14295/524288)]

def upper0834 : ℚ := (24792219/1048576000000000)

def plusWeights0834 : Fin 11 → ℚ := ![(24792219/1048576000000000), (24792219/104857600000000), (223129971/209715200000000), (74376657/26214400000000), (520636599/104857600000000), (1561909797/262144000000000), (522940599/104857600000000), (76719057/26214400000000), (251738931/209715200000000), (6902007/20971520000000), (24792219/524288000000000)]

def minusWeights0834 : Fin 11 → ℚ := ![(24792219/1048576000000000), (24792219/104857600000000), (223129971/209715200000000), (74376657/26214400000000), (520636599/104857600000000), (1561909797/262144000000000), (518332599/104857600000000), (72034257/26214400000000), (194521011/209715200000000), (15074403/104857600000000), 0]

theorem checked0834 :
    (∀ i, 0 ≤ plusWeights0834 i) ∧
    (∀ i, 0 ≤ minusWeights0834 i) ∧
    (∀ i, plusCoefficients coefficients0834 upper0834 i = powerCoefficients10 plusWeights0834 i) ∧
    (∀ i, minusCoefficients coefficients0834 upper0834 i = powerCoefficients10 minusWeights0834 i) := by
  decide +kernel

theorem bound0834 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0834 g| ≤ (upper0834 : ℝ) :=
  abs_of_coefficients coefficients0834 upper0834 powerCoefficients10 plusWeights0834 minusWeights0834
    checked0834.1 checked0834.2.1 checked0834.2.2.1 checked0834.2.2.2
    (power_identity10 plusWeights0834) (power_identity10 minusWeights0834) g hg hmax

def envelope0834 : Envelope := ⟨coefficients0834, upper0834, bound0834⟩

def coefficients0835 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/2048), (15/1024), (945/32768), (1245/65536), (13065/524288)]

def upper0835 : ℚ := (24900933/1048576000000000)

def plusWeights0835 : Fin 11 → ℚ := ![(24900933/1048576000000000), (24900933/104857600000000), (224108397/209715200000000), (74702799/26214400000000), (522919593/104857600000000), (1568758779/262144000000000), (525223593/104857600000000), (77045199/26214400000000), (252738477/209715200000000), (6928041/20971520000000), (24900933/524288000000000)]

def minusWeights0835 : Fin 11 → ℚ := ![(24900933/1048576000000000), (24900933/104857600000000), (224108397/209715200000000), (74702799/26214400000000), (522919593/104857600000000), (1568758779/262144000000000), (520615593/104857600000000), (72360399/26214400000000), (195478317/209715200000000), (15161661/104857600000000), 0]

theorem checked0835 :
    (∀ i, 0 ≤ plusWeights0835 i) ∧
    (∀ i, 0 ≤ minusWeights0835 i) ∧
    (∀ i, plusCoefficients coefficients0835 upper0835 i = powerCoefficients10 plusWeights0835 i) ∧
    (∀ i, minusCoefficients coefficients0835 upper0835 i = powerCoefficients10 minusWeights0835 i) := by
  decide +kernel

theorem bound0835 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0835 g| ≤ (upper0835 : ℝ) :=
  abs_of_coefficients coefficients0835 upper0835 powerCoefficients10 plusWeights0835 minusWeights0835
    checked0835.1 checked0835.2.1 checked0835.2.2.1 checked0835.2.2.2
    (power_identity10 plusWeights0835) (power_identity10 minusWeights0835) g hg hmax

def envelope0835 : Envelope := ⟨coefficients0835, upper0835, bound0835⟩

def coefficients0836 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/1024), (-93/4096), (291/4096), (267/8192), (4365/262144)]

def upper0836 : ℚ := (13024041/524288000000000)

def plusWeights0836 : Fin 11 → ℚ := ![(13024041/524288000000000), (13024041/52428800000000), (117216369/104857600000000), (39072123/13107200000000), (273504861/52428800000000), (820514583/131072000000000), (274887261/52428800000000), (40424763/13107200000000), (5326617/4194304000000), (91363629/262144000000000), (13024041/262144000000000)]

def minusWeights0836 : Fin 11 → ℚ := ![(13024041/524288000000000), (13024041/52428800000000), (117216369/104857600000000), (39072123/13107200000000), (273504861/52428800000000), (820514583/131072000000000), (272122461/52428800000000), (37719483/13107200000000), (101267313/104857600000000), (38876781/262144000000000), 0]

theorem checked0836 :
    (∀ i, 0 ≤ plusWeights0836 i) ∧
    (∀ i, 0 ≤ minusWeights0836 i) ∧
    (∀ i, plusCoefficients coefficients0836 upper0836 i = powerCoefficients10 plusWeights0836 i) ∧
    (∀ i, minusCoefficients coefficients0836 upper0836 i = powerCoefficients10 minusWeights0836 i) := by
  decide +kernel

theorem bound0836 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0836 g| ≤ (upper0836 : ℝ) :=
  abs_of_coefficients coefficients0836 upper0836 powerCoefficients10 plusWeights0836 minusWeights0836
    checked0836.1 checked0836.2.1 checked0836.2.2.1 checked0836.2.2.2
    (power_identity10 plusWeights0836) (power_identity10 minusWeights0836) g hg hmax

def envelope0836 : Envelope := ⟨coefficients0836, upper0836, bound0836⟩

def coefficients0837 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/1024), (39/8192), (1773/32768), (1701/65536), (10335/524288)]

def upper0837 : ℚ := (28743843/1048576000000000)

def plusWeights0837 : Fin 11 → ℚ := ![(28743843/1048576000000000), (28743843/104857600000000), (258694587/209715200000000), (86231529/26214400000000), (603620703/104857600000000), (1810862109/262144000000000), (606385503/104857600000000), (89008809/26214400000000), (292285179/209715200000000), (200344983/524288000000000), (28743843/524288000000000)]

def minusWeights0837 : Fin 11 → ℚ := ![(28743843/1048576000000000), (28743843/104857600000000), (258694587/209715200000000), (86231529/26214400000000), (603620703/104857600000000), (1810862109/262144000000000), (600855903/104857600000000), (83454249/26214400000000), (45020799/41943040000000), (87093447/524288000000000), 0]

theorem checked0837 :
    (∀ i, 0 ≤ plusWeights0837 i) ∧
    (∀ i, 0 ≤ minusWeights0837 i) ∧
    (∀ i, plusCoefficients coefficients0837 upper0837 i = powerCoefficients10 plusWeights0837 i) ∧
    (∀ i, minusCoefficients coefficients0837 upper0837 i = powerCoefficients10 minusWeights0837 i) := by
  decide +kernel

theorem bound0837 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0837 g| ≤ (upper0837 : ℝ) :=
  abs_of_coefficients coefficients0837 upper0837 powerCoefficients10 plusWeights0837 minusWeights0837
    checked0837.1 checked0837.2.1 checked0837.2.2.1 checked0837.2.2.2
    (power_identity10 plusWeights0837) (power_identity10 minusWeights0837) g hg hmax

def envelope0837 : Envelope := ⟨coefficients0837, upper0837, bound0837⟩

def coefficients0838 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/1024), (39/8192), (2163/32768), (2331/65536), (18795/524288)]

def upper0838 : ℚ := (5776083/209715200000000)

def plusWeights0838 : Fin 11 → ℚ := ![(5776083/209715200000000), (5776083/20971520000000), (51984747/41943040000000), (17328249/5242880000000), (121297743/20971520000000), (363893229/52428800000000), (121850703/20971520000000), (3576741/1048576000000), (293539287/209715200000000), (201157683/524288000000000), (5776083/104857600000000)]

def minusWeights0838 : Fin 11 → ℚ := ![(5776083/209715200000000), (5776083/20971520000000), (51984747/41943040000000), (17328249/5242880000000), (121297743/20971520000000), (363893229/52428800000000), (120744783/20971520000000), (16772793/5242880000000), (226308183/209715200000000), (87646467/524288000000000), 0]

theorem checked0838 :
    (∀ i, 0 ≤ plusWeights0838 i) ∧
    (∀ i, 0 ≤ minusWeights0838 i) ∧
    (∀ i, plusCoefficients coefficients0838 upper0838 i = powerCoefficients10 plusWeights0838 i) ∧
    (∀ i, minusCoefficients coefficients0838 upper0838 i = powerCoefficients10 minusWeights0838 i) := by
  decide +kernel

theorem bound0838 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0838 g| ≤ (upper0838 : ℝ) :=
  abs_of_coefficients coefficients0838 upper0838 powerCoefficients10 plusWeights0838 minusWeights0838
    checked0838.1 checked0838.2.1 checked0838.2.2.1 checked0838.2.2.2
    (power_identity10 plusWeights0838) (power_identity10 minusWeights0838) g hg hmax

def envelope0838 : Envelope := ⟨coefficients0838, upper0838, bound0838⟩

def coefficients0839 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/256), (163/4096), (21/1024), (1/64), (15/4096)]

def upper0839 : ℚ := (258411/8192000000000)

def plusWeights0839 : Fin 11 → ℚ := ![(258411/8192000000000), (258411/819200000000), (2325699/1638400000000), (775233/204800000000), (5426631/819200000000), (16279893/2048000000000), (5449031/819200000000), (49903/12800000000), (522879/327680000000), (1790699/4096000000000), (258411/4096000000000)]

def minusWeights0839 : Fin 11 → ℚ := ![(258411/8192000000000), (258411/819200000000), (2325699/1638400000000), (775233/204800000000), (5426631/819200000000), (16279893/2048000000000), (5404231/819200000000), (376009/102400000000), (2037003/1638400000000), (793411/4096000000000), 0]

theorem checked0839 :
    (∀ i, 0 ≤ plusWeights0839 i) ∧
    (∀ i, 0 ≤ minusWeights0839 i) ∧
    (∀ i, plusCoefficients coefficients0839 upper0839 i = powerCoefficients10 plusWeights0839 i) ∧
    (∀ i, minusCoefficients coefficients0839 upper0839 i = powerCoefficients10 minusWeights0839 i) := by
  decide +kernel

theorem bound0839 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0839 g| ≤ (upper0839 : ℝ) :=
  abs_of_coefficients coefficients0839 upper0839 powerCoefficients10 plusWeights0839 minusWeights0839
    checked0839.1 checked0839.2.1 checked0839.2.2.1 checked0839.2.2.2
    (power_identity10 plusWeights0839) (power_identity10 minusWeights0839) g hg hmax

def envelope0839 : Envelope := ⟨coefficients0839, upper0839, bound0839⟩

def coefficients0840 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/512), (-15/1024), (-15/512), (-135/8192), (-75/16384)]

def upper0840 : ℚ := (180369/6553600000000)

def plusWeights0840 : Fin 11 → ℚ := ![(180369/6553600000000), (180369/655360000000), (1623321/1310720000000), (541107/163840000000), (3787749/655360000000), (11363247/1638400000000), (3806949/655360000000), (560067/163840000000), (1847577/1310720000000), (1269471/3276800000000), (180369/3276800000000)]

def minusWeights0840 : Fin 11 → ℚ := ![(180369/6553600000000), (180369/655360000000), (1623321/1310720000000), (541107/163840000000), (3787749/655360000000), (11363247/1638400000000), (3768549/655360000000), (522147/163840000000), (279813/262144000000), (534219/3276800000000), 0]

theorem checked0840 :
    (∀ i, 0 ≤ plusWeights0840 i) ∧
    (∀ i, 0 ≤ minusWeights0840 i) ∧
    (∀ i, plusCoefficients coefficients0840 upper0840 i = powerCoefficients10 plusWeights0840 i) ∧
    (∀ i, minusCoefficients coefficients0840 upper0840 i = powerCoefficients10 minusWeights0840 i) := by
  decide +kernel

theorem bound0840 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0840 g| ≤ (upper0840 : ℝ) :=
  abs_of_coefficients coefficients0840 upper0840 powerCoefficients10 plusWeights0840 minusWeights0840
    checked0840.1 checked0840.2.1 checked0840.2.2.1 checked0840.2.2.2
    (power_identity10 plusWeights0840) (power_identity10 minusWeights0840) g hg hmax

def envelope0840 : Envelope := ⟨coefficients0840, upper0840, bound0840⟩

def coefficients0841 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/512), (5/256), (515/16384), (675/32768), (1925/262144)]

def upper0841 : ℚ := (3311997/104857600000000)

def plusWeights0841 : Fin 11 → ℚ := ![(3311997/104857600000000), (3311997/10485760000000), (29807973/20971520000000), (9935991/2621440000000), (69551937/10485760000000), (208655811/26214400000000), (69859137/10485760000000), (10248311/2621440000000), (6724769/4194304000000), (921809/2097152000000), (3311997/52428800000000)]

def minusWeights0841 : Fin 11 → ℚ := ![(3311997/104857600000000), (3311997/10485760000000), (29807973/20971520000000), (9935991/2621440000000), (69551937/10485760000000), (208655811/26214400000000), (69244737/10485760000000), (9623671/2621440000000), (25992101/20971520000000), (2014949/10485760000000), 0]

theorem checked0841 :
    (∀ i, 0 ≤ plusWeights0841 i) ∧
    (∀ i, 0 ≤ minusWeights0841 i) ∧
    (∀ i, plusCoefficients coefficients0841 upper0841 i = powerCoefficients10 plusWeights0841 i) ∧
    (∀ i, minusCoefficients coefficients0841 upper0841 i = powerCoefficients10 minusWeights0841 i) := by
  decide +kernel

theorem bound0841 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0841 g| ≤ (upper0841 : ℝ) :=
  abs_of_coefficients coefficients0841 upper0841 powerCoefficients10 plusWeights0841 minusWeights0841
    checked0841.1 checked0841.2.1 checked0841.2.2.1 checked0841.2.2.2
    (power_identity10 plusWeights0841) (power_identity10 minusWeights0841) g hg hmax

def envelope0841 : Envelope := ⟨coefficients0841, upper0841, bound0841⟩

def coefficients0842 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/32), (369/8192), (167/8192), (157/8192), (155/32768)]

def upper0842 : ℚ := (2357847/65536000000000)

def plusWeights0842 : Fin 11 → ℚ := ![(2357847/65536000000000), (2357847/6553600000000), (21220623/13107200000000), (7073541/1638400000000), (49514787/6553600000000), (148544361/16384000000000), (49719587/6553600000000), (7285721/1638400000000), (4771603/2621440000000), (16342023/32768000000000), (2357847/32768000000000)]

def minusWeights0842 : Fin 11 → ℚ := ![(2357847/65536000000000), (2357847/6553600000000), (21220623/13107200000000), (7073541/1638400000000), (49514787/6553600000000), (148544361/16384000000000), (49309987/6553600000000), (6861361/1638400000000), (18583231/13107200000000), (7236447/32768000000000), 0]

theorem checked0842 :
    (∀ i, 0 ≤ plusWeights0842 i) ∧
    (∀ i, 0 ≤ minusWeights0842 i) ∧
    (∀ i, plusCoefficients coefficients0842 upper0842 i = powerCoefficients10 plusWeights0842 i) ∧
    (∀ i, minusCoefficients coefficients0842 upper0842 i = powerCoefficients10 minusWeights0842 i) := by
  decide +kernel

theorem bound0842 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0842 g| ≤ (upper0842 : ℝ) :=
  abs_of_coefficients coefficients0842 upper0842 powerCoefficients10 plusWeights0842 minusWeights0842
    checked0842.1 checked0842.2.1 checked0842.2.2.1 checked0842.2.2.2
    (power_identity10 plusWeights0842) (power_identity10 minusWeights0842) g hg hmax

def envelope0842 : Envelope := ⟨coefficients0842, upper0842, bound0842⟩

def coefficients0843 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/32), (3/64), (37/512), (27/512), (25/2048)]

def upper0843 : ℚ := (150381/4096000000000)

def plusWeights0843 : Fin 11 → ℚ := ![(150381/4096000000000), (150381/409600000000), (1353429/819200000000), (451143/102400000000), (3158001/409600000000), (9474003/1024000000000), (3170801/409600000000), (464423/102400000000), (1519141/819200000000), (1039773/2048000000000), (150381/2048000000000)]

def minusWeights0843 : Fin 11 → ℚ := ![(150381/4096000000000), (150381/409600000000), (1353429/819200000000), (451143/102400000000), (3158001/409600000000), (9474003/1024000000000), (3145201/409600000000), (437863/102400000000), (1187717/819200000000), (464037/2048000000000), 0]

theorem checked0843 :
    (∀ i, 0 ≤ plusWeights0843 i) ∧
    (∀ i, 0 ≤ minusWeights0843 i) ∧
    (∀ i, plusCoefficients coefficients0843 upper0843 i = powerCoefficients10 plusWeights0843 i) ∧
    (∀ i, minusCoefficients coefficients0843 upper0843 i = powerCoefficients10 minusWeights0843 i) := by
  decide +kernel

theorem bound0843 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0843 g| ≤ (upper0843 : ℝ) :=
  abs_of_coefficients coefficients0843 upper0843 powerCoefficients10 plusWeights0843 minusWeights0843
    checked0843.1 checked0843.2.1 checked0843.2.2.1 checked0843.2.2.2
    (power_identity10 plusWeights0843) (power_identity10 minusWeights0843) g hg hmax

def envelope0843 : Envelope := ⟨coefficients0843, upper0843, bound0843⟩

def coefficients0844 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/32), (3/64), (21/256), (1/16), (15/1024)]

def upper0844 : ℚ := (75411/2048000000000)

def plusWeights0844 : Fin 11 → ℚ := ![(75411/2048000000000), (75411/204800000000), (678699/409600000000), (226233/51200000000), (1583631/204800000000), (4750893/512000000000), (1590031/204800000000), (232873/51200000000), (152319/81920000000), (521199/1024000000000), (75411/1024000000000)]

def minusWeights0844 : Fin 11 → ℚ := ![(75411/2048000000000), (75411/204800000000), (678699/409600000000), (226233/51200000000), (1583631/204800000000), (4750893/512000000000), (1577231/204800000000), (219593/51200000000), (595803/409600000000), (232911/1024000000000), 0]

theorem checked0844 :
    (∀ i, 0 ≤ plusWeights0844 i) ∧
    (∀ i, 0 ≤ minusWeights0844 i) ∧
    (∀ i, plusCoefficients coefficients0844 upper0844 i = powerCoefficients10 plusWeights0844 i) ∧
    (∀ i, minusCoefficients coefficients0844 upper0844 i = powerCoefficients10 minusWeights0844 i) := by
  decide +kernel

theorem bound0844 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0844 g| ≤ (upper0844 : ℝ) :=
  abs_of_coefficients coefficients0844 upper0844 powerCoefficients10 plusWeights0844 minusWeights0844
    checked0844.1 checked0844.2.1 checked0844.2.2.1 checked0844.2.2.2
    (power_identity10 plusWeights0844) (power_identity10 minusWeights0844) g hg hmax

def envelope0844 : Envelope := ⟨coefficients0844, upper0844, bound0844⟩

def coefficients0845 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/128), (15/256), (45/512), (65/1024), (15/1024)]

def upper0845 : ℚ := (93933/2048000000000)

def plusWeights0845 : Fin 11 → ℚ := ![(93933/2048000000000), (93933/204800000000), (845397/409600000000), (281799/51200000000), (1972593/204800000000), (5917779/512000000000), (1980593/204800000000), (290099/51200000000), (948957/409600000000), (64953/102400000000), (93933/1024000000000)]

def minusWeights0845 : Fin 11 → ℚ := ![(93933/2048000000000), (93933/204800000000), (845397/409600000000), (281799/51200000000), (1972593/204800000000), (5917779/512000000000), (1964593/204800000000), (273499/51200000000), (741837/409600000000), (1449/5120000000), 0]

theorem checked0845 :
    (∀ i, 0 ≤ plusWeights0845 i) ∧
    (∀ i, 0 ≤ minusWeights0845 i) ∧
    (∀ i, plusCoefficients coefficients0845 upper0845 i = powerCoefficients10 plusWeights0845 i) ∧
    (∀ i, minusCoefficients coefficients0845 upper0845 i = powerCoefficients10 minusWeights0845 i) := by
  decide +kernel

theorem bound0845 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0845 g| ≤ (upper0845 : ℝ) :=
  abs_of_coefficients coefficients0845 upper0845 powerCoefficients10 plusWeights0845 minusWeights0845
    checked0845.1 checked0845.2.1 checked0845.2.2.1 checked0845.2.2.2
    (power_identity10 plusWeights0845) (power_identity10 minusWeights0845) g hg hmax

def envelope0845 : Envelope := ⟨coefficients0845, upper0845, bound0845⟩

def coefficients0846 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (5/128), (15/256), (25/256), (75/1024), (35/2048)]

def upper0846 : ℚ := (188307/4096000000000)

def plusWeights0846 : Fin 11 → ℚ := ![(188307/4096000000000), (188307/409600000000), (1694763/819200000000), (564921/102400000000), (3954447/409600000000), (11863341/1024000000000), (3970447/409600000000), (581521/102400000000), (1901963/819200000000), (260337/409600000000), (188307/2048000000000)]

def minusWeights0846 : Fin 11 → ℚ := ![(188307/4096000000000), (188307/409600000000), (1694763/819200000000), (564921/102400000000), (3954447/409600000000), (11863341/1024000000000), (3938447/409600000000), (548321/102400000000), (1487563/819200000000), (116277/409600000000), 0]

theorem checked0846 :
    (∀ i, 0 ≤ plusWeights0846 i) ∧
    (∀ i, 0 ≤ minusWeights0846 i) ∧
    (∀ i, plusCoefficients coefficients0846 upper0846 i = powerCoefficients10 plusWeights0846 i) ∧
    (∀ i, minusCoefficients coefficients0846 upper0846 i = powerCoefficients10 minusWeights0846 i) := by
  decide +kernel

theorem bound0846 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0846 g| ≤ (upper0846 : ℝ) :=
  abs_of_coefficients coefficients0846 upper0846 powerCoefficients10 plusWeights0846 minusWeights0846
    checked0846.1 checked0846.2.1 checked0846.2.2.1 checked0846.2.2.2
    (power_identity10 plusWeights0846) (power_identity10 minusWeights0846) g hg hmax

def envelope0846 : Envelope := ⟨coefficients0846, upper0846, bound0846⟩

def coefficients0847 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/512), (489/8192), (39/1024), (63/2048), (15/2048)]

def upper0847 : ℚ := (194139/4096000000000)

def plusWeights0847 : Fin 11 → ℚ := ![(194139/4096000000000), (194139/409600000000), (1747251/819200000000), (582417/102400000000), (4076919/409600000000), (12230757/1024000000000), (4093719/409600000000), (2399313/409600000000), (1963833/819200000000), (1344993/2048000000000), (194139/2048000000000)]

def minusWeights0847 : Fin 11 → ℚ := ![(194139/4096000000000), (194139/409600000000), (1747251/819200000000), (582417/102400000000), (4076919/409600000000), (12230757/1024000000000), (4060119/409600000000), (2260023/409600000000), (1530669/819200000000), (596397/2048000000000), 0]

theorem checked0847 :
    (∀ i, 0 ≤ plusWeights0847 i) ∧
    (∀ i, 0 ≤ minusWeights0847 i) ∧
    (∀ i, plusCoefficients coefficients0847 upper0847 i = powerCoefficients10 plusWeights0847 i) ∧
    (∀ i, minusCoefficients coefficients0847 upper0847 i = powerCoefficients10 minusWeights0847 i) := by
  decide +kernel

theorem bound0847 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0847 g| ≤ (upper0847 : ℝ) :=
  abs_of_coefficients coefficients0847 upper0847 powerCoefficients10 plusWeights0847 minusWeights0847
    checked0847.1 checked0847.2.1 checked0847.2.2.1 checked0847.2.2.2
    (power_identity10 plusWeights0847) (power_identity10 minusWeights0847) g hg hmax

def envelope0847 : Envelope := ⟨coefficients0847, upper0847, bound0847⟩

def coefficients0848 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/512), (489/8192), (27/512), (93/2048), (45/4096)]

def upper0848 : ℚ := (389601/8192000000000)

def plusWeights0848 : Fin 11 → ℚ := ![(389601/8192000000000), (389601/819200000000), (3506409/1638400000000), (1168803/204800000000), (8181621/819200000000), (24544863/2048000000000), (8215221/819200000000), (2407251/409600000000), (3939813/1638400000000), (2697861/4096000000000), (389601/4096000000000)]

def minusWeights0848 : Fin 11 → ℚ := ![(389601/8192000000000), (389601/819200000000), (3506409/1638400000000), (1168803/204800000000), (8181621/819200000000), (24544863/2048000000000), (8148021/819200000000), (2267961/409600000000), (614601/327680000000), (1198149/4096000000000), 0]

theorem checked0848 :
    (∀ i, 0 ≤ plusWeights0848 i) ∧
    (∀ i, 0 ≤ minusWeights0848 i) ∧
    (∀ i, plusCoefficients coefficients0848 upper0848 i = powerCoefficients10 plusWeights0848 i) ∧
    (∀ i, minusCoefficients coefficients0848 upper0848 i = powerCoefficients10 minusWeights0848 i) := by
  decide +kernel

theorem bound0848 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0848 g| ≤ (upper0848 : ℝ) :=
  abs_of_coefficients coefficients0848 upper0848 powerCoefficients10 plusWeights0848 minusWeights0848
    checked0848.1 checked0848.2.1 checked0848.2.2.1 checked0848.2.2.2
    (power_identity10 plusWeights0848) (power_identity10 minusWeights0848) g hg hmax

def envelope0848 : Envelope := ⟨coefficients0848, upper0848, bound0848⟩

def coefficients0849 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/512), (357/4096), (63/2048), (3/128), (45/8192)]

def upper0849 : ℚ := (820233/16384000000000)

def plusWeights0849 : Fin 11 → ℚ := ![(820233/16384000000000), (820233/1638400000000), (7382097/3276800000000), (2460699/409600000000), (17224893/1638400000000), (51674679/4096000000000), (17292093/1638400000000), (2531469/409600000000), (1655037/655360000000), (5664597/8192000000000), (820233/8192000000000)]

def minusWeights0849 : Fin 11 → ℚ := ![(820233/16384000000000), (820233/1638400000000), (7382097/3276800000000), (2460699/409600000000), (17224893/1638400000000), (51674679/4096000000000), (17157693/1638400000000), (2389929/409600000000), (6489009/3276800000000), (2537733/8192000000000), 0]

theorem checked0849 :
    (∀ i, 0 ≤ plusWeights0849 i) ∧
    (∀ i, 0 ≤ minusWeights0849 i) ∧
    (∀ i, plusCoefficients coefficients0849 upper0849 i = powerCoefficients10 plusWeights0849 i) ∧
    (∀ i, minusCoefficients coefficients0849 upper0849 i = powerCoefficients10 minusWeights0849 i) := by
  decide +kernel

theorem bound0849 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0849 g| ≤ (upper0849 : ℝ) :=
  abs_of_coefficients coefficients0849 upper0849 powerCoefficients10 plusWeights0849 minusWeights0849
    checked0849.1 checked0849.2.1 checked0849.2.2.1 checked0849.2.2.2
    (power_identity10 plusWeights0849) (power_identity10 minusWeights0849) g hg hmax

def envelope0849 : Envelope := ⟨coefficients0849, upper0849, bound0849⟩

def coefficients0850 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (43/1024), (381/8192), (13/512), (109/4096), (55/8192)]

def upper0850 : ℚ := (768807/16384000000000)

def plusWeights0850 : Fin 11 → ℚ := ![(768807/16384000000000), (768807/1638400000000), (6919263/3276800000000), (2306421/409600000000), (16144947/1638400000000), (48434841/4096000000000), (16213747/1638400000000), (1188563/204800000000), (1558283/655360000000), (5338713/8192000000000), (768807/8192000000000)]

def minusWeights0850 : Fin 11 → ℚ := ![(768807/16384000000000), (768807/1638400000000), (6919263/3276800000000), (2306421/409600000000), (16144947/1638400000000), (48434841/4096000000000), (16076147/1638400000000), (558929/102400000000), (6047111/3276800000000), (2349357/8192000000000), 0]

theorem checked0850 :
    (∀ i, 0 ≤ plusWeights0850 i) ∧
    (∀ i, 0 ≤ minusWeights0850 i) ∧
    (∀ i, plusCoefficients coefficients0850 upper0850 i = powerCoefficients10 plusWeights0850 i) ∧
    (∀ i, minusCoefficients coefficients0850 upper0850 i = powerCoefficients10 minusWeights0850 i) := by
  decide +kernel

theorem bound0850 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0850 g| ≤ (upper0850 : ℝ) :=
  abs_of_coefficients coefficients0850 upper0850 powerCoefficients10 plusWeights0850 minusWeights0850
    checked0850.1 checked0850.2.1 checked0850.2.2.1 checked0850.2.2.2
    (power_identity10 plusWeights0850) (power_identity10 minusWeights0850) g hg hmax

def envelope0850 : Envelope := ⟨coefficients0850, upper0850, bound0850⟩

def coefficients0851 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (43/1024), (381/8192), (239/4096), (61/1024), (245/16384)]

def upper0851 : ℚ := (1549521/32768000000000)

def plusWeights0851 : Fin 11 → ℚ := ![(1549521/32768000000000), (1549521/3276800000000), (13945689/6553600000000), (4648563/819200000000), (32539941/3276800000000), (97619823/8192000000000), (32677541/3276800000000), (4789973/819200000000), (15692153/6553600000000), (10748301/16384000000000), (1549521/16384000000000)]

def minusWeights0851 : Fin 11 → ℚ := ![(1549521/32768000000000), (1549521/3276800000000), (13945689/6553600000000), (4648563/819200000000), (32539941/3276800000000), (97619823/8192000000000), (32402341/3276800000000), (4507153/819200000000), (487969/262144000000), (4746909/16384000000000), 0]

theorem checked0851 :
    (∀ i, 0 ≤ plusWeights0851 i) ∧
    (∀ i, 0 ≤ minusWeights0851 i) ∧
    (∀ i, plusCoefficients coefficients0851 upper0851 i = powerCoefficients10 plusWeights0851 i) ∧
    (∀ i, minusCoefficients coefficients0851 upper0851 i = powerCoefficients10 minusWeights0851 i) := by
  decide +kernel

theorem bound0851 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0851 g| ≤ (upper0851 : ℝ) :=
  abs_of_coefficients coefficients0851 upper0851 powerCoefficients10 plusWeights0851 minusWeights0851
    checked0851.1 checked0851.2.1 checked0851.2.2.1 checked0851.2.2.2
    (power_identity10 plusWeights0851) (power_identity10 minusWeights0851) g hg hmax

def envelope0851 : Envelope := ⟨coefficients0851, upper0851, bound0851⟩

def coefficients0852 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/1024), (15/512), (45/2048), (75/4096), (825/262144)]

def upper0852 : ℚ := (4940193/104857600000000)

def plusWeights0852 : Fin 11 → ℚ := ![(4940193/104857600000000), (4940193/10485760000000), (44461737/20971520000000), (14820579/2621440000000), (103744053/10485760000000), (311232159/26214400000000), (104204853/10485760000000), (15289059/2621440000000), (10036053/4194304000000), (6880353/10485760000000), (4940193/52428800000000)]

def minusWeights0852 : Fin 11 → ℚ := ![(4940193/104857600000000), (4940193/10485760000000), (44461737/20971520000000), (14820579/2621440000000), (103744053/10485760000000), (311232159/26214400000000), (103283253/10485760000000), (14352099/2621440000000), (38743209/20971520000000), (3000033/10485760000000), 0]

theorem checked0852 :
    (∀ i, 0 ≤ plusWeights0852 i) ∧
    (∀ i, 0 ≤ minusWeights0852 i) ∧
    (∀ i, plusCoefficients coefficients0852 upper0852 i = powerCoefficients10 plusWeights0852 i) ∧
    (∀ i, minusCoefficients coefficients0852 upper0852 i = powerCoefficients10 minusWeights0852 i) := by
  decide +kernel

theorem bound0852 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0852 g| ≤ (upper0852 : ℝ) :=
  abs_of_coefficients coefficients0852 upper0852 powerCoefficients10 plusWeights0852 minusWeights0852
    checked0852.1 checked0852.2.1 checked0852.2.2.1 checked0852.2.2.2
    (power_identity10 plusWeights0852) (power_identity10 minusWeights0852) g hg hmax

def envelope0852 : Envelope := ⟨coefficients0852, upper0852, bound0852⟩

def coefficients0853 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/1024), (15/512), (1065/32768), (1665/65536), (7755/524288)]

def upper0853 : ℚ := (49520991/1048576000000000)

def plusWeights0853 : Fin 11 → ℚ := ![(49520991/1048576000000000), (49520991/104857600000000), (445688919/209715200000000), (148562973/26214400000000), (1039940811/104857600000000), (3119822433/262144000000000), (1044548811/104857600000000), (153247773/26214400000000), (502896279/209715200000000), (13789083/20971520000000), (49520991/524288000000000)]

def minusWeights0853 : Fin 11 → ℚ := ![(49520991/1048576000000000), (49520991/104857600000000), (445688919/209715200000000), (148562973/26214400000000), (1039940811/104857600000000), (3119822433/262144000000000), (1035332811/104857600000000), (143878173/26214400000000), (388481559/209715200000000), (30096567/104857600000000), 0]

theorem checked0853 :
    (∀ i, 0 ≤ plusWeights0853 i) ∧
    (∀ i, 0 ≤ minusWeights0853 i) ∧
    (∀ i, plusCoefficients coefficients0853 upper0853 i = powerCoefficients10 plusWeights0853 i) ∧
    (∀ i, minusCoefficients coefficients0853 upper0853 i = powerCoefficients10 minusWeights0853 i) := by
  decide +kernel

theorem bound0853 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0853 g| ≤ (upper0853 : ℝ) :=
  abs_of_coefficients coefficients0853 upper0853 powerCoefficients10 plusWeights0853 minusWeights0853
    checked0853.1 checked0853.2.1 checked0853.2.2.1 checked0853.2.2.2
    (power_identity10 plusWeights0853) (power_identity10 minusWeights0853) g hg hmax

def envelope0853 : Envelope := ⟨coefficients0853, upper0853, bound0853⟩

def coefficients0854 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/1024), (15/512), (1455/32768), (2295/65536), (16215/524288)]

def upper0854 : ℚ := (49657563/1048576000000000)

def plusWeights0854 : Fin 11 → ℚ := ![(49657563/1048576000000000), (49657563/104857600000000), (446918067/209715200000000), (148972689/26214400000000), (1042808823/104857600000000), (3128426469/262144000000000), (1047416823/104857600000000), (153657489/26214400000000), (504150387/209715200000000), (13821591/20971520000000), (49657563/524288000000000)]

def minusWeights0854 : Fin 11 → ℚ := ![(49657563/1048576000000000), (49657563/104857600000000), (446918067/209715200000000), (148972689/26214400000000), (1042808823/104857600000000), (3128426469/262144000000000), (1038200823/104857600000000), (144287889/26214400000000), (389685747/209715200000000), (30207171/104857600000000), 0]

theorem checked0854 :
    (∀ i, 0 ≤ plusWeights0854 i) ∧
    (∀ i, 0 ≤ minusWeights0854 i) ∧
    (∀ i, plusCoefficients coefficients0854 upper0854 i = powerCoefficients10 plusWeights0854 i) ∧
    (∀ i, minusCoefficients coefficients0854 upper0854 i = powerCoefficients10 minusWeights0854 i) := by
  decide +kernel

theorem bound0854 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0854 g| ≤ (upper0854 : ℝ) :=
  abs_of_coefficients coefficients0854 upper0854 powerCoefficients10 plusWeights0854 minusWeights0854
    checked0854.1 checked0854.2.1 checked0854.2.2.1 checked0854.2.2.2
    (power_identity10 plusWeights0854) (power_identity10 minusWeights0854) g hg hmax

def envelope0854 : Envelope := ⟨coefficients0854, upper0854, bound0854⟩

def coefficients0855 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/512), (39/4096), (1353/16384), (1161/32768), (3855/262144)]

def upper0855 : ℚ := (28599507/524288000000000)

def plusWeights0855 : Fin 11 → ℚ := ![(28599507/524288000000000), (28599507/52428800000000), (257395563/104857600000000), (85798521/13107200000000), (600589647/52428800000000), (1801768941/131072000000000), (603354447/52428800000000), (88575801/13107200000000), (11638371/4194304000000), (199484583/262144000000000), (28599507/262144000000000)]

def minusWeights0855 : Fin 11 → ℚ := ![(28599507/524288000000000), (28599507/52428800000000), (257395563/104857600000000), (85798521/13107200000000), (600589647/52428800000000), (1801768941/131072000000000), (597824847/52428800000000), (83021241/13107200000000), (223831851/104857600000000), (86510487/262144000000000), 0]

theorem checked0855 :
    (∀ i, 0 ≤ plusWeights0855 i) ∧
    (∀ i, 0 ≤ minusWeights0855 i) ∧
    (∀ i, plusCoefficients coefficients0855 upper0855 i = powerCoefficients10 plusWeights0855 i) ∧
    (∀ i, minusCoefficients coefficients0855 upper0855 i = powerCoefficients10 minusWeights0855 i) := by
  decide +kernel

theorem bound0855 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0855 g| ≤ (upper0855 : ℝ) :=
  abs_of_coefficients coefficients0855 upper0855 powerCoefficients10 plusWeights0855 minusWeights0855
    checked0855.1 checked0855.2.1 checked0855.2.2.1 checked0855.2.2.2
    (power_identity10 plusWeights0855) (power_identity10 minusWeights0855) g hg hmax

def envelope0855 : Envelope := ⟨coefficients0855, upper0855, bound0855⟩

def coefficients0856 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/512), (39/4096), (1503/16384), (1311/32768), (4605/262144)]

def upper0856 : ℚ := (28650057/524288000000000)

def plusWeights0856 : Fin 11 → ℚ := ![(28650057/524288000000000), (28650057/52428800000000), (257850513/104857600000000), (85950171/13107200000000), (601651197/52428800000000), (1804953591/131072000000000), (604415997/52428800000000), (88727451/13107200000000), (11656953/4194304000000), (199786533/262144000000000), (28650057/262144000000000)]

def minusWeights0856 : Fin 11 → ℚ := ![(28650057/524288000000000), (28650057/52428800000000), (257850513/104857600000000), (85950171/13107200000000), (601651197/52428800000000), (1804953591/131072000000000), (598886397/52428800000000), (83172891/13107200000000), (224277201/104857600000000), (86714037/262144000000000), 0]

theorem checked0856 :
    (∀ i, 0 ≤ plusWeights0856 i) ∧
    (∀ i, 0 ≤ minusWeights0856 i) ∧
    (∀ i, plusCoefficients coefficients0856 upper0856 i = powerCoefficients10 plusWeights0856 i) ∧
    (∀ i, minusCoefficients coefficients0856 upper0856 i = powerCoefficients10 minusWeights0856 i) := by
  decide +kernel

theorem bound0856 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0856 g| ≤ (upper0856 : ℝ) :=
  abs_of_coefficients coefficients0856 upper0856 powerCoefficients10 plusWeights0856 minusWeights0856
    checked0856.1 checked0856.2.1 checked0856.2.2.1 checked0856.2.2.2
    (power_identity10 plusWeights0856) (power_identity10 minusWeights0856) g hg hmax

def envelope0856 : Envelope := ⟨coefficients0856, upper0856, bound0856⟩

def coefficients0857 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/16), (369/4096), (167/4096), (157/4096), (155/16384)]

def upper0857 : ℚ := (2357847/32768000000000)

def plusWeights0857 : Fin 11 → ℚ := ![(2357847/32768000000000), (2357847/3276800000000), (21220623/6553600000000), (7073541/819200000000), (49514787/3276800000000), (148544361/8192000000000), (49719587/3276800000000), (7285721/819200000000), (4771603/1310720000000), (16342023/16384000000000), (2357847/16384000000000)]

def minusWeights0857 : Fin 11 → ℚ := ![(2357847/32768000000000), (2357847/3276800000000), (21220623/6553600000000), (7073541/819200000000), (49514787/3276800000000), (148544361/8192000000000), (49309987/3276800000000), (6861361/819200000000), (18583231/6553600000000), (7236447/16384000000000), 0]

theorem checked0857 :
    (∀ i, 0 ≤ plusWeights0857 i) ∧
    (∀ i, 0 ≤ minusWeights0857 i) ∧
    (∀ i, plusCoefficients coefficients0857 upper0857 i = powerCoefficients10 plusWeights0857 i) ∧
    (∀ i, minusCoefficients coefficients0857 upper0857 i = powerCoefficients10 minusWeights0857 i) := by
  decide +kernel

theorem bound0857 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0857 g| ≤ (upper0857 : ℝ) :=
  abs_of_coefficients coefficients0857 upper0857 powerCoefficients10 plusWeights0857 minusWeights0857
    checked0857.1 checked0857.2.1 checked0857.2.2.1 checked0857.2.2.2
    (power_identity10 plusWeights0857) (power_identity10 minusWeights0857) g hg hmax

def envelope0857 : Envelope := ⟨coefficients0857, upper0857, bound0857⟩

def coefficients0858 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/16), (3/32), (1/8), (11/128), (5/256)]

def upper0858 : ℚ := (7497/102400000000)

def plusWeights0858 : Fin 11 → ℚ := ![(7497/102400000000), (7497/10240000000), (67473/20480000000), (22491/2560000000), (157437/10240000000), (472311/25600000000), (158077/10240000000), (4631/512000000), (378773/102400000000), (259287/256000000000), (7497/51200000000)]

def minusWeights0858 : Fin 11 → ℚ := ![(7497/102400000000), (7497/10240000000), (67473/20480000000), (22491/2560000000), (157437/10240000000), (472311/25600000000), (156797/10240000000), (21827/2560000000), (295957/102400000000), (115563/256000000000), 0]

theorem checked0858 :
    (∀ i, 0 ≤ plusWeights0858 i) ∧
    (∀ i, 0 ≤ minusWeights0858 i) ∧
    (∀ i, plusCoefficients coefficients0858 upper0858 i = powerCoefficients10 plusWeights0858 i) ∧
    (∀ i, minusCoefficients coefficients0858 upper0858 i = powerCoefficients10 minusWeights0858 i) := by
  decide +kernel

theorem bound0858 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0858 g| ≤ (upper0858 : ℝ) :=
  abs_of_coefficients coefficients0858 upper0858 powerCoefficients10 plusWeights0858 minusWeights0858
    checked0858.1 checked0858.2.1 checked0858.2.2.1 checked0858.2.2.2
    (power_identity10 plusWeights0858) (power_identity10 minusWeights0858) g hg hmax

def envelope0858 : Envelope := ⟨coefficients0858, upper0858, bound0858⟩

def coefficients0859 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/512), (15/256), (645/16384), (1125/32768), (1275/262144)]

def upper0859 : ℚ := (9875331/104857600000000)

def plusWeights0859 : Fin 11 → ℚ := ![(9875331/104857600000000), (9875331/10485760000000), (88877979/20971520000000), (29625993/2621440000000), (207381951/10485760000000), (622145853/26214400000000), (208303551/10485760000000), (30562953/2621440000000), (4012563/838860800000), (13754667/10485760000000), (9875331/52428800000000)]

def minusWeights0859 : Fin 11 → ℚ := ![(9875331/104857600000000), (9875331/10485760000000), (88877979/20971520000000), (29625993/2621440000000), (207381951/10485760000000), (622145853/26214400000000), (206460351/10485760000000), (28689033/2621440000000), (77441883/20971520000000), (1199199/2097152000000), 0]

theorem checked0859 :
    (∀ i, 0 ≤ plusWeights0859 i) ∧
    (∀ i, 0 ≤ minusWeights0859 i) ∧
    (∀ i, plusCoefficients coefficients0859 upper0859 i = powerCoefficients10 plusWeights0859 i) ∧
    (∀ i, minusCoefficients coefficients0859 upper0859 i = powerCoefficients10 minusWeights0859 i) := by
  decide +kernel

theorem bound0859 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0859 g| ≤ (upper0859 : ℝ) :=
  abs_of_coefficients coefficients0859 upper0859 powerCoefficients10 plusWeights0859 minusWeights0859
    checked0859.1 checked0859.2.1 checked0859.2.2.1 checked0859.2.2.2
    (power_identity10 plusWeights0859) (power_identity10 minusWeights0859) g hg hmax

def envelope0859 : Envelope := ⟨coefficients0859, upper0859, bound0859⟩

def coefficients0860 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/512), (15/256), (795/16384), (1275/32768), (2025/262144)]

def upper0860 : ℚ := (9885441/104857600000000)

def plusWeights0860 : Fin 11 → ℚ := ![(9885441/104857600000000), (9885441/10485760000000), (88968969/20971520000000), (29656323/2621440000000), (207594261/10485760000000), (622782783/26214400000000), (208515861/10485760000000), (30593283/2621440000000), (20081397/4194304000000), (2753349/2097152000000), (9885441/52428800000000)]

def minusWeights0860 : Fin 11 → ℚ := ![(9885441/104857600000000), (9885441/10485760000000), (88968969/20971520000000), (29656323/2621440000000), (207594261/10485760000000), (622782783/26214400000000), (206672661/10485760000000), (28719363/2621440000000), (77530953/20971520000000), (6004137/10485760000000), 0]

theorem checked0860 :
    (∀ i, 0 ≤ plusWeights0860 i) ∧
    (∀ i, 0 ≤ minusWeights0860 i) ∧
    (∀ i, plusCoefficients coefficients0860 upper0860 i = powerCoefficients10 plusWeights0860 i) ∧
    (∀ i, minusCoefficients coefficients0860 upper0860 i = powerCoefficients10 minusWeights0860 i) := by
  decide +kernel

theorem bound0860 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0860 g| ≤ (upper0860 : ℝ) :=
  abs_of_coefficients coefficients0860 upper0860 powerCoefficients10 plusWeights0860 minusWeights0860
    checked0860.1 checked0860.2.1 checked0860.2.2.1 checked0860.2.2.2
    (power_identity10 plusWeights0860) (power_identity10 minusWeights0860) g hg hmax

def envelope0860 : Envelope := ⟨coefficients0860, upper0860, bound0860⟩

def coefficients0861 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/128), (19/512), (11/512), (1005/32768), (1325/65536), (3725/524288)]

def upper0861 : ℚ := (24685669/209715200000000)

def plusWeights0861 : Fin 11 → ℚ := ![(24685669/209715200000000), (24685669/20971520000000), (222171021/41943040000000), (74057007/5242880000000), (518399049/20971520000000), (1559293147/52428800000000), (527369289/20971520000000), (78942511/5242880000000), (264561101/41943040000000), (7227817/4194304000000), (24685669/104857600000000)]

def minusWeights0861 : Fin 11 → ℚ := ![(24685669/209715200000000), (24685669/20971520000000), (222171021/41943040000000), (74057007/5242880000000), (518399049/20971520000000), (1551101147/52428800000000), (509428809/20971520000000), (69171503/5242880000000), (179780941/41943040000000), (13232253/20971520000000), 0]

theorem checked0861 :
    (∀ i, 0 ≤ plusWeights0861 i) ∧
    (∀ i, 0 ≤ minusWeights0861 i) ∧
    (∀ i, plusCoefficients coefficients0861 upper0861 i = powerCoefficients10 plusWeights0861 i) ∧
    (∀ i, minusCoefficients coefficients0861 upper0861 i = powerCoefficients10 minusWeights0861 i) := by
  decide +kernel

theorem bound0861 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0861 g| ≤ (upper0861 : ℝ) :=
  abs_of_coefficients coefficients0861 upper0861 powerCoefficients10 plusWeights0861 minusWeights0861
    checked0861.1 checked0861.2.1 checked0861.2.2.1 checked0861.2.2.2
    (power_identity10 plusWeights0861) (power_identity10 minusWeights0861) g hg hmax

def envelope0861 : Envelope := ⟨coefficients0861, upper0861, bound0861⟩

def coefficients0862 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/128), (53/1024), (1/32), (945/32768), (1425/65536), (2775/524288)]

def upper0862 : ℚ := (27958911/209715200000000)

def plusWeights0862 : Fin 11 → ℚ := ![(27958911/209715200000000), (27958911/20971520000000), (251630199/41943040000000), (83876733/5242880000000), (587137131/20971520000000), (1765507393/52428800000000), (596414571/20971520000000), (89074557/5242880000000), (297828791/41943040000000), (40701831/20971520000000), (27958911/104857600000000)]

def minusWeights0862 : Fin 11 → ℚ := ![(27958911/209715200000000), (27958911/20971520000000), (251630199/41943040000000), (83876733/5242880000000), (587137131/20971520000000), (1757315393/52428800000000), (577859691/20971520000000), (78678909/5242880000000), (205431607/41943040000000), (15215991/20971520000000), 0]

theorem checked0862 :
    (∀ i, 0 ≤ plusWeights0862 i) ∧
    (∀ i, 0 ≤ minusWeights0862 i) ∧
    (∀ i, plusCoefficients coefficients0862 upper0862 i = powerCoefficients10 plusWeights0862 i) ∧
    (∀ i, minusCoefficients coefficients0862 upper0862 i = powerCoefficients10 minusWeights0862 i) := by
  decide +kernel

theorem bound0862 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0862 g| ≤ (upper0862 : ℝ) :=
  abs_of_coefficients coefficients0862 upper0862 powerCoefficients10 plusWeights0862 minusWeights0862
    checked0862.1 checked0862.2.1 checked0862.2.2.1 checked0862.2.2.2
    (power_identity10 plusWeights0862) (power_identity10 minusWeights0862) g hg hmax

def envelope0862 : Envelope := ⟨coefficients0862, upper0862, bound0862⟩

def coefficients0863 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (5/512), (3/256), (69/8192), (21/4096), (1/256), (15/16384)]

def upper0863 : ℚ := (3613411/32768000000000)

def plusWeights0863 : Fin 11 → ℚ := ![(3613411/32768000000000), (3613411/3276800000000), (32520699/6553600000000), (10840233/819200000000), (75881631/3276800000000), (228444893/8192000000000), (77520031/3276800000000), (11679323/819200000000), (7879679/1310720000000), (26878199/16384000000000), (3613411/16384000000000)]

def minusWeights0863 : Fin 11 → ℚ := ![(3613411/32768000000000), (3613411/3276800000000), (32520699/6553600000000), (10840233/819200000000), (75881631/3276800000000), (226844893/8192000000000), (74243231/3276800000000), (10001143/819200000000), (25643003/6553600000000), (9255911/16384000000000), 0]

theorem checked0863 :
    (∀ i, 0 ≤ plusWeights0863 i) ∧
    (∀ i, 0 ≤ minusWeights0863 i) ∧
    (∀ i, plusCoefficients coefficients0863 upper0863 i = powerCoefficients10 plusWeights0863 i) ∧
    (∀ i, minusCoefficients coefficients0863 upper0863 i = powerCoefficients10 minusWeights0863 i) := by
  decide +kernel

theorem bound0863 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0863 g| ≤ (upper0863 : ℝ) :=
  abs_of_coefficients coefficients0863 upper0863 powerCoefficients10 plusWeights0863 minusWeights0863
    checked0863.1 checked0863.2.1 checked0863.2.2.1 checked0863.2.2.2
    (power_identity10 plusWeights0863) (power_identity10 minusWeights0863) g hg hmax

def envelope0863 : Envelope := ⟨coefficients0863, upper0863, bound0863⟩

end BilayerDressed.CubicQuarticEnvelopes

import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0864 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (5/512), (19/1024), (113/8192), (21/2048), (1/128), (15/8192)]

def upper0864 : ℚ := (1928411/16384000000000)

def plusWeights0864 : Fin 11 → ℚ := ![(1928411/16384000000000), (1928411/1638400000000), (17355699/3276800000000), (5785233/409600000000), (40496631/1638400000000), (121889893/4096000000000), (41327031/1638400000000), (3108099/204800000000), (4186879/655360000000), (14285699/8192000000000), (1928411/8192000000000)]

def minusWeights0864 : Fin 11 → ℚ := ![(1928411/16384000000000), (1928411/1638400000000), (17355699/3276800000000), (5785233/409600000000), (40496631/1638400000000), (121089893/4096000000000), (39666231/1638400000000), (1338567/102400000000), (13777003/3276800000000), (4998411/8192000000000), 0]

theorem checked0864 :
    (∀ i, 0 ≤ plusWeights0864 i) ∧
    (∀ i, 0 ≤ minusWeights0864 i) ∧
    (∀ i, plusCoefficients coefficients0864 upper0864 i = powerCoefficients10 plusWeights0864 i) ∧
    (∀ i, minusCoefficients coefficients0864 upper0864 i = powerCoefficients10 minusWeights0864 i) := by
  decide +kernel

theorem bound0864 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0864 g| ≤ (upper0864 : ℝ) :=
  abs_of_coefficients coefficients0864 upper0864 powerCoefficients10 plusWeights0864 minusWeights0864
    checked0864.1 checked0864.2.1 checked0864.2.2.1 checked0864.2.2.2
    (power_identity10 plusWeights0864) (power_identity10 minusWeights0864) g hg hmax

def envelope0864 : Envelope := ⟨coefficients0864, upper0864, bound0864⟩

def coefficients0865 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/64), (107/2048), (29/1024), (575/16384), (775/32768), (4125/524288)]

def upper0865 : ℚ := (8879489/41943040000000)

def plusWeights0865 : Fin 11 → ℚ := ![(8879489/41943040000000), (8879489/4194304000000), (79915401/8388608000000), (26638467/1048576000000), (186469269/4194304000000), (561046207/10485760000000), (37993041/838860800000), (142494863/5242880000000), (478632237/41943040000000), (65357557/20971520000000), (8879489/20971520000000)]

def minusWeights0865 : Fin 11 → ℚ := ![(8879489/41943040000000), (8879489/4194304000000), (79915401/8388608000000), (26638467/1048576000000), (186469269/4194304000000), (557769407/10485760000000), (182973333/4194304000000), (123889807/5242880000000), (320521773/41943040000000), (23437333/20971520000000), 0]

theorem checked0865 :
    (∀ i, 0 ≤ plusWeights0865 i) ∧
    (∀ i, 0 ≤ minusWeights0865 i) ∧
    (∀ i, plusCoefficients coefficients0865 upper0865 i = powerCoefficients10 plusWeights0865 i) ∧
    (∀ i, minusCoefficients coefficients0865 upper0865 i = powerCoefficients10 minusWeights0865 i) := by
  decide +kernel

theorem bound0865 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0865 g| ≤ (upper0865 : ℝ) :=
  abs_of_coefficients coefficients0865 upper0865 powerCoefficients10 plusWeights0865 minusWeights0865
    checked0865.1 checked0865.2.1 checked0865.2.2.1 checked0865.2.2.2
    (power_identity10 plusWeights0865) (power_identity10 minusWeights0865) g hg hmax

def envelope0865 : Envelope := ⟨coefficients0865, upper0865, bound0865⟩

def coefficients0866 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/64), (167/2048), (49/1024), (345/8192), (525/16384), (3975/524288)]

def upper0866 : ℚ := (50967519/209715200000000)

def plusWeights0866 : Fin 11 → ℚ := ![(50967519/209715200000000), (50967519/20971520000000), (458707671/41943040000000), (152902557/5242880000000), (1070317899/20971520000000), (3219145697/52428800000000), (1088411979/20971520000000), (6513189/209715200000), (545384407/41943040000000), (74511231/20971520000000), (50967519/104857600000000)]

def minusWeights0866 : Fin 11 → ℚ := ![(50967519/209715200000000), (50967519/20971520000000), (458707671/41943040000000), (152902557/5242880000000), (1070317899/20971520000000), (3202761697/52428800000000), (1052223819/20971520000000), (142975389/5242880000000), (74406187/8388608000000), (27423807/20971520000000), 0]

theorem checked0866 :
    (∀ i, 0 ≤ plusWeights0866 i) ∧
    (∀ i, 0 ≤ minusWeights0866 i) ∧
    (∀ i, plusCoefficients coefficients0866 upper0866 i = powerCoefficients10 plusWeights0866 i) ∧
    (∀ i, minusCoefficients coefficients0866 upper0866 i = powerCoefficients10 minusWeights0866 i) := by
  decide +kernel

theorem bound0866 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0866 g| ≤ (upper0866 : ℝ) :=
  abs_of_coefficients coefficients0866 upper0866 powerCoefficients10 plusWeights0866 minusWeights0866
    checked0866.1 checked0866.2.1 checked0866.2.2.1 checked0866.2.2.2
    (power_identity10 plusWeights0866) (power_identity10 minusWeights0866) g hg hmax

def envelope0866 : Envelope := ⟨coefficients0866, upper0866, bound0866⟩

def coefficients0867 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/64), (167/2048), (49/1024), (2595/32768), (3855/65536), (24135/524288)]

def upper0867 : ℚ := (255258507/1048576000000000)

def plusWeights0867 : Fin 11 → ℚ := ![(255258507/1048576000000000), (255258507/104857600000000), (2297326563/209715200000000), (765775521/26214400000000), (5360428647/104857600000000), (16122245941/262144000000000), (5450899047/104857600000000), (815411361/26214400000000), (2730788003/209715200000000), (74611527/20971520000000), (255258507/524288000000000)]

def minusWeights0867 : Fin 11 → ℚ := ![(255258507/1048576000000000), (255258507/104857600000000), (2297326563/209715200000000), (765775521/26214400000000), (5360428647/104857600000000), (16040325941/262144000000000), (5269958247/104857600000000), (716139681/26214400000000), (1863865123/209715200000000), (137459379/104857600000000), 0]

theorem checked0867 :
    (∀ i, 0 ≤ plusWeights0867 i) ∧
    (∀ i, 0 ≤ minusWeights0867 i) ∧
    (∀ i, plusCoefficients coefficients0867 upper0867 i = powerCoefficients10 plusWeights0867 i) ∧
    (∀ i, minusCoefficients coefficients0867 upper0867 i = powerCoefficients10 minusWeights0867 i) := by
  decide +kernel

theorem bound0867 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0867 g| ≤ (upper0867 : ℝ) :=
  abs_of_coefficients coefficients0867 upper0867 powerCoefficients10 plusWeights0867 minusWeights0867
    checked0867.1 checked0867.2.1 checked0867.2.2.1 checked0867.2.2.2
    (power_identity10 plusWeights0867) (power_identity10 minusWeights0867) g hg hmax

def envelope0867 : Envelope := ⟨coefficients0867, upper0867, bound0867⟩

def coefficients0868 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/64), (53/512), (1/16), (945/16384), (1425/32768), (2775/262144)]

def upper0868 : ℚ := (27958911/104857600000000)

def plusWeights0868 : Fin 11 → ℚ := ![(27958911/104857600000000), (27958911/10485760000000), (251630199/20971520000000), (83876733/2621440000000), (587137131/10485760000000), (1765507393/26214400000000), (596414571/10485760000000), (89074557/2621440000000), (297828791/20971520000000), (40701831/10485760000000), (27958911/52428800000000)]

def minusWeights0868 : Fin 11 → ℚ := ![(27958911/104857600000000), (27958911/10485760000000), (251630199/20971520000000), (83876733/2621440000000), (587137131/10485760000000), (1757315393/26214400000000), (577859691/10485760000000), (78678909/2621440000000), (205431607/20971520000000), (15215991/10485760000000), 0]

theorem checked0868 :
    (∀ i, 0 ≤ plusWeights0868 i) ∧
    (∀ i, 0 ≤ minusWeights0868 i) ∧
    (∀ i, plusCoefficients coefficients0868 upper0868 i = powerCoefficients10 plusWeights0868 i) ∧
    (∀ i, minusCoefficients coefficients0868 upper0868 i = powerCoefficients10 minusWeights0868 i) := by
  decide +kernel

theorem bound0868 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0868 g| ≤ (upper0868 : ℝ) :=
  abs_of_coefficients coefficients0868 upper0868 powerCoefficients10 plusWeights0868 minusWeights0868
    checked0868.1 checked0868.2.1 checked0868.2.2.1 checked0868.2.2.2
    (power_identity10 plusWeights0868) (power_identity10 minusWeights0868) g hg hmax

def envelope0868 : Envelope := ⟨coefficients0868, upper0868, bound0868⟩

def coefficients0869 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (15/512), (57/1024), (339/8192), (63/2048), (3/128), (45/8192)]

def upper0869 : ℚ := (5785233/16384000000000)

def plusWeights0869 : Fin 11 → ℚ := ![(5785233/16384000000000), (5785233/1638400000000), (52067097/3276800000000), (17355699/409600000000), (121489893/1638400000000), (365669679/4096000000000), (123981093/1638400000000), (9324297/204800000000), (12560637/655360000000), (42857097/8192000000000), (5785233/8192000000000)]

def minusWeights0869 : Fin 11 → ℚ := ![(5785233/16384000000000), (5785233/1638400000000), (52067097/3276800000000), (17355699/409600000000), (121489893/1638400000000), (363269679/4096000000000), (118998693/1638400000000), (4015701/102400000000), (41331009/3276800000000), (14995233/8192000000000), 0]

theorem checked0869 :
    (∀ i, 0 ≤ plusWeights0869 i) ∧
    (∀ i, 0 ≤ minusWeights0869 i) ∧
    (∀ i, plusCoefficients coefficients0869 upper0869 i = powerCoefficients10 plusWeights0869 i) ∧
    (∀ i, minusCoefficients coefficients0869 upper0869 i = powerCoefficients10 minusWeights0869 i) := by
  decide +kernel

theorem bound0869 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0869 g| ≤ (upper0869 : ℝ) :=
  abs_of_coefficients coefficients0869 upper0869 powerCoefficients10 plusWeights0869 minusWeights0869
    checked0869.1 checked0869.2.1 checked0869.2.2.1 checked0869.2.2.2
    (power_identity10 plusWeights0869) (power_identity10 minusWeights0869) g hg hmax

def envelope0869 : Envelope := ⟨coefficients0869, upper0869, bound0869⟩

def coefficients0870 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/32), (61/512), (17/256), (1815/32768), (2775/65536), (5175/524288)]

def upper0870 : ℚ := (92039487/209715200000000)

def plusWeights0870 : Fin 11 → ℚ := ![(92039487/209715200000000), (92039487/20971520000000), (828355383/41943040000000), (276118461/5242880000000), (1932829227/20971520000000), (5814871681/52428800000000), (1968095787/20971520000000), (295035837/5242880000000), (990268919/41943040000000), (135243639/20971520000000), (92039487/104857600000000)]

def minusWeights0870 : Fin 11 → ℚ := ![(92039487/209715200000000), (92039487/20971520000000), (828355383/41943040000000), (276118461/5242880000000), (1932829227/20971520000000), (5782103681/52428800000000), (1897562667/20971520000000), (51440217/1048576000000), (666441847/41943040000000), (9767067/4194304000000), 0]

theorem checked0870 :
    (∀ i, 0 ≤ plusWeights0870 i) ∧
    (∀ i, 0 ≤ minusWeights0870 i) ∧
    (∀ i, plusCoefficients coefficients0870 upper0870 i = powerCoefficients10 plusWeights0870 i) ∧
    (∀ i, minusCoefficients coefficients0870 upper0870 i = powerCoefficients10 minusWeights0870 i) := by
  decide +kernel

theorem bound0870 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0870 g| ≤ (upper0870 : ℝ) :=
  abs_of_coefficients coefficients0870 upper0870 powerCoefficients10 plusWeights0870 minusWeights0870
    checked0870.1 checked0870.2.1 checked0870.2.2.1 checked0870.2.2.2
    (power_identity10 plusWeights0870) (power_identity10 minusWeights0870) g hg hmax

def envelope0870 : Envelope := ⟨coefficients0870, upper0870, bound0870⟩

def coefficients0871 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/32), (61/512), (17/256), (2355/32768), (3555/65536), (12135/524288)]

def upper0871 : ℚ := (460384107/1048576000000000)

def plusWeights0871 : Fin 11 → ℚ := ![(460384107/1048576000000000), (460384107/104857600000000), (4143456963/209715200000000), (1381152321/26214400000000), (9668066247/104857600000000), (29086118741/262144000000000), (9844399047/104857600000000), (1475739201/26214400000000), (4953059203/209715200000000), (27057627/4194304000000), (460384107/524288000000000)]

def minusWeights0871 : Fin 11 → ℚ := ![(460384107/1048576000000000), (460384107/104857600000000), (4143456963/209715200000000), (1381152321/26214400000000), (9668066247/104857600000000), (28922278741/262144000000000), (9491733447/104857600000000), (1286565441/26214400000000), (3333854723/209715200000000), (244327539/104857600000000), 0]

theorem checked0871 :
    (∀ i, 0 ≤ plusWeights0871 i) ∧
    (∀ i, 0 ≤ minusWeights0871 i) ∧
    (∀ i, plusCoefficients coefficients0871 upper0871 i = powerCoefficients10 plusWeights0871 i) ∧
    (∀ i, minusCoefficients coefficients0871 upper0871 i = powerCoefficients10 minusWeights0871 i) := by
  decide +kernel

theorem bound0871 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0871 g| ≤ (upper0871 : ℝ) :=
  abs_of_coefficients coefficients0871 upper0871 powerCoefficients10 plusWeights0871 minusWeights0871
    checked0871.1 checked0871.2.1 checked0871.2.2.1 checked0871.2.2.2
    (power_identity10 plusWeights0871) (power_identity10 minusWeights0871) g hg hmax

def envelope0871 : Envelope := ⟨coefficients0871, upper0871, bound0871⟩

def coefficients0872 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (5/128), (19/256), (113/2048), (21/512), (1/32), (15/2048)]

def upper0872 : ℚ := (1928411/4096000000000)

def plusWeights0872 : Fin 11 → ℚ := ![(1928411/4096000000000), (1928411/409600000000), (17355699/819200000000), (5785233/102400000000), (40496631/409600000000), (121889893/1024000000000), (41327031/409600000000), (3108099/51200000000), (4186879/163840000000), (14285699/2048000000000), (1928411/2048000000000)]

def minusWeights0872 : Fin 11 → ℚ := ![(1928411/4096000000000), (1928411/409600000000), (17355699/819200000000), (5785233/102400000000), (40496631/409600000000), (121089893/1024000000000), (39666231/409600000000), (1338567/25600000000), (13777003/819200000000), (4998411/2048000000000), 0]

theorem checked0872 :
    (∀ i, 0 ≤ plusWeights0872 i) ∧
    (∀ i, 0 ≤ minusWeights0872 i) ∧
    (∀ i, plusCoefficients coefficients0872 upper0872 i = powerCoefficients10 plusWeights0872 i) ∧
    (∀ i, minusCoefficients coefficients0872 upper0872 i = powerCoefficients10 minusWeights0872 i) := by
  decide +kernel

theorem bound0872 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0872 g| ≤ (upper0872 : ℝ) :=
  abs_of_coefficients coefficients0872 upper0872 powerCoefficients10 plusWeights0872 minusWeights0872
    checked0872.1 checked0872.2.1 checked0872.2.2.1 checked0872.2.2.2
    (power_identity10 plusWeights0872) (power_identity10 minusWeights0872) g hg hmax

def envelope0872 : Envelope := ⟨coefficients0872, upper0872, bound0872⟩

def coefficients0873 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (15/256), (57/512), (339/4096), (63/1024), (3/64), (45/4096)]

def upper0873 : ℚ := (5785233/8192000000000)

def plusWeights0873 : Fin 11 → ℚ := ![(5785233/8192000000000), (5785233/819200000000), (52067097/1638400000000), (17355699/204800000000), (121489893/819200000000), (365669679/2048000000000), (123981093/819200000000), (9324297/102400000000), (12560637/327680000000), (42857097/4096000000000), (5785233/4096000000000)]

def minusWeights0873 : Fin 11 → ℚ := ![(5785233/8192000000000), (5785233/819200000000), (52067097/1638400000000), (17355699/204800000000), (121489893/819200000000), (363269679/2048000000000), (118998693/819200000000), (4015701/51200000000), (41331009/1638400000000), (14995233/4096000000000), 0]

theorem checked0873 :
    (∀ i, 0 ≤ plusWeights0873 i) ∧
    (∀ i, 0 ≤ minusWeights0873 i) ∧
    (∀ i, plusCoefficients coefficients0873 upper0873 i = powerCoefficients10 plusWeights0873 i) ∧
    (∀ i, minusCoefficients coefficients0873 upper0873 i = powerCoefficients10 minusWeights0873 i) := by
  decide +kernel

theorem bound0873 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0873 g| ≤ (upper0873 : ℝ) :=
  abs_of_coefficients coefficients0873 upper0873 powerCoefficients10 plusWeights0873 minusWeights0873
    checked0873.1 checked0873.2.1 checked0873.2.2.1 checked0873.2.2.2
    (power_identity10 plusWeights0873) (power_identity10 minusWeights0873) g hg hmax

def envelope0873 : Envelope := ⟨coefficients0873, upper0873, bound0873⟩

def coefficients0874 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/64), (-23/512), (-19/512), (-797/8192), (-391/4096), (-4413/65536), (-2641/131072)]

def upper0874 : ℚ := (1396465899/1310720000000000)

def plusWeights0874 : Fin 11 → ℚ := ![(1396465899/1310720000000000), (1396465899/131072000000000), (12568193091/262144000000000), (4189397697/32768000000000), (29530583879/131072000000000), (90902151637/327680000000000), (32098519879/131072000000000), (5061014897/32768000000000), (17468323651/262144000000000), (2307325233/131072000000000), (1396465899/655360000000000)]

def minusWeights0874 : Fin 11 → ℚ := ![(1396465899/1310720000000000), (1396465899/131072000000000), (12568193091/262144000000000), (4189397697/32768000000000), (29120983879/131072000000000), (85052551637/327680000000000), (26553047879/131072000000000), (3317780497/32768000000000), (7668062531/262144000000000), (97121313/26214400000000), 0]

theorem checked0874 :
    (∀ i, 0 ≤ plusWeights0874 i) ∧
    (∀ i, 0 ≤ minusWeights0874 i) ∧
    (∀ i, plusCoefficients coefficients0874 upper0874 i = powerCoefficients10 plusWeights0874 i) ∧
    (∀ i, minusCoefficients coefficients0874 upper0874 i = powerCoefficients10 minusWeights0874 i) := by
  decide +kernel

theorem bound0874 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0874 g| ≤ (upper0874 : ℝ) :=
  abs_of_coefficients coefficients0874 upper0874 powerCoefficients10 plusWeights0874 minusWeights0874
    checked0874.1 checked0874.2.1 checked0874.2.2.1 checked0874.2.2.2
    (power_identity10 plusWeights0874) (power_identity10 minusWeights0874) g hg hmax

def envelope0874 : Envelope := ⟨coefficients0874, upper0874, bound0874⟩

def coefficients0875 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/64), (-19/512), (-21/512), (-609/8192), (-217/4096), (-1695/65536), (-875/131072)]

def upper0875 : ℚ := (59894673/52428800000000)

def plusWeights0875 : Fin 11 → ℚ := ![(59894673/52428800000000), (59894673/5242880000000), (539052057/10485760000000), (179684019/1310720000000), (1265980133/5242880000000), (3891380399/13107200000000), (1370725093/5242880000000), (43111047/262144000000), (3715400829/52428800000000), (491679471/26214400000000), (59894673/26214400000000)]

def minusWeights0875 : Fin 11 → ℚ := ![(59894673/52428800000000), (59894673/5242880000000), (539052057/10485760000000), (179684019/1310720000000), (1249596133/5242880000000), (3655348399/13107200000000), (1144851173/5242880000000), (143812803/1310720000000), (1675119741/52428800000000), (107267259/26214400000000), 0]

theorem checked0875 :
    (∀ i, 0 ≤ plusWeights0875 i) ∧
    (∀ i, 0 ≤ minusWeights0875 i) ∧
    (∀ i, plusCoefficients coefficients0875 upper0875 i = powerCoefficients10 plusWeights0875 i) ∧
    (∀ i, minusCoefficients coefficients0875 upper0875 i = powerCoefficients10 minusWeights0875 i) := by
  decide +kernel

theorem bound0875 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0875 g| ≤ (upper0875 : ℝ) :=
  abs_of_coefficients coefficients0875 upper0875 powerCoefficients10 plusWeights0875 minusWeights0875
    checked0875.1 checked0875.2.1 checked0875.2.2.1 checked0875.2.2.2
    (power_identity10 plusWeights0875) (power_identity10 minusWeights0875) g hg hmax

def envelope0875 : Envelope := ⟨coefficients0875, upper0875, bound0875⟩

def coefficients0876 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/64), (-15/512), (-15/512), (-491/8192), (-89/2048), (-715/32768), (-375/65536)]

def upper0876 : ℚ := (32342901/26214400000000)

def plusWeights0876 : Fin 11 → ℚ := ![(32342901/26214400000000), (32342901/2621440000000), (291086109/5242880000000), (97028703/655360000000), (683296921/2621440000000), (2097122763/6553600000000), (736724121/2621440000000), (4620319/26214400000), (1987939793/26214400000000), (263611147/13107200000000), (32342901/13107200000000)]

def minusWeights0876 : Fin 11 → ℚ := ![(32342901/26214400000000), (32342901/2621440000000), (291086109/5242880000000), (97028703/655360000000), (675104921/2621440000000), (1978082763/6553600000000), (621677721/2621440000000), (78549431/655360000000), (922921297/26214400000000), (59817863/13107200000000), 0]

theorem checked0876 :
    (∀ i, 0 ≤ plusWeights0876 i) ∧
    (∀ i, 0 ≤ minusWeights0876 i) ∧
    (∀ i, plusCoefficients coefficients0876 upper0876 i = powerCoefficients10 plusWeights0876 i) ∧
    (∀ i, minusCoefficients coefficients0876 upper0876 i = powerCoefficients10 minusWeights0876 i) := by
  decide +kernel

theorem bound0876 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0876 g| ≤ (upper0876 : ℝ) :=
  abs_of_coefficients coefficients0876 upper0876 powerCoefficients10 plusWeights0876 minusWeights0876
    checked0876.1 checked0876.2.1 checked0876.2.2.1 checked0876.2.2.2
    (power_identity10 plusWeights0876) (power_identity10 minusWeights0876) g hg hmax

def envelope0876 : Envelope := ⟨coefficients0876, upper0876, bound0876⟩

def coefficients0877 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/64), (-5/512), (-5/256), (-411/8192), (-163/4096), (-1295/65536), (-675/131072)]

def upper0877 : ℚ := (75491033/52428800000000)

def plusWeights0877 : Fin 11 → ℚ := ![(75491033/52428800000000), (75491033/5242880000000), (679419297/10485760000000), (226473099/1310720000000), (1593503693/5242880000000), (4877535079/13107200000000), (1705529293/5242880000000), (266044123/1310720000000), (4567742501/52428800000000), (607951223/26214400000000), (75491033/26214400000000)]

def minusWeights0877 : Fin 11 → ℚ := ![(75491033/52428800000000), (75491033/5242880000000), (679419297/10485760000000), (226473099/1310720000000), (1577119693/5242880000000), (4634335079/13107200000000), (1465094093/5242880000000), (7476083/52428800000), (2226450469/52428800000000), (146959107/26214400000000), 0]

theorem checked0877 :
    (∀ i, 0 ≤ plusWeights0877 i) ∧
    (∀ i, 0 ≤ minusWeights0877 i) ∧
    (∀ i, plusCoefficients coefficients0877 upper0877 i = powerCoefficients10 plusWeights0877 i) ∧
    (∀ i, minusCoefficients coefficients0877 upper0877 i = powerCoefficients10 minusWeights0877 i) := by
  decide +kernel

theorem bound0877 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0877 g| ≤ (upper0877 : ℝ) :=
  abs_of_coefficients coefficients0877 upper0877 powerCoefficients10 plusWeights0877 minusWeights0877
    checked0877.1 checked0877.2.1 checked0877.2.2.1 checked0877.2.2.2
    (power_identity10 plusWeights0877) (power_identity10 minusWeights0877) g hg hmax

def envelope0877 : Envelope := ⟨coefficients0877, upper0877, bound0877⟩

def coefficients0878 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/128), (-1/512), (3/128), (141/8192), (63/1024), (613/16384), (8115/262144)]

def upper0878 : ℚ := (1232094199/524288000000000)

def plusWeights0878 : Fin 11 → ℚ := ![(1232094199/524288000000000), (1232094199/52428800000000), (11088847791/104857600000000), (3696282597/13107200000000), (25996858179/52428800000000), (79462574537/131072000000000), (27713286979/52428800000000), (4309373957/13107200000000), (14770119343/104857600000000), (9847532963/262144000000000), (1232094199/262144000000000)]

def minusWeights0878 : Fin 11 → ℚ := ![(1232094199/524288000000000), (1232094199/52428800000000), (11088847791/104857600000000), (3696282597/13107200000000), (25751098179/52428800000000), (75781294537/131072000000000), (24034669379/52428800000000), (3083191237/13107200000000), (7407576239/104857600000000), (2473409027/262144000000000), 0]

theorem checked0878 :
    (∀ i, 0 ≤ plusWeights0878 i) ∧
    (∀ i, 0 ≤ minusWeights0878 i) ∧
    (∀ i, plusCoefficients coefficients0878 upper0878 i = powerCoefficients10 plusWeights0878 i) ∧
    (∀ i, minusCoefficients coefficients0878 upper0878 i = powerCoefficients10 minusWeights0878 i) := by
  decide +kernel

theorem bound0878 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0878 g| ≤ (upper0878 : ℝ) :=
  abs_of_coefficients coefficients0878 upper0878 powerCoefficients10 plusWeights0878 minusWeights0878
    checked0878.1 checked0878.2.1 checked0878.2.2.1 checked0878.2.2.2
    (power_identity10 plusWeights0878) (power_identity10 minusWeights0878) g hg hmax

def envelope0878 : Envelope := ⟨coefficients0878, upper0878, bound0878⟩

def coefficients0879 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/128), (-1/512), (53/1024), (409/8192), (543/8192), (531/16384), (1095/65536)]

def upper0879 : ℚ := (312169747/131072000000000)

def plusWeights0879 : Fin 11 → ℚ := ![(312169747/131072000000000), (312169747/13107200000000), (2809527723/26214400000000), (936509241/3276800000000), (6586284687/13107200000000), (20126854061/32768000000000), (7015763087/13107200000000), (1090164001/3276800000000), (3734558539/26214400000000), (2490687339/65536000000000), (312169747/65536000000000)]

def minusWeights0879 : Fin 11 → ℚ := ![(312169747/131072000000000), (312169747/13107200000000), (2809527723/26214400000000), (936509241/3276800000000), (6524844687/13107200000000), (19206534061/32768000000000), (6095366287/13107200000000), (782854481/3276800000000), (1884496907/26214400000000), (631010131/65536000000000), 0]

theorem checked0879 :
    (∀ i, 0 ≤ plusWeights0879 i) ∧
    (∀ i, 0 ≤ minusWeights0879 i) ∧
    (∀ i, plusCoefficients coefficients0879 upper0879 i = powerCoefficients10 plusWeights0879 i) ∧
    (∀ i, minusCoefficients coefficients0879 upper0879 i = powerCoefficients10 minusWeights0879 i) := by
  decide +kernel

theorem bound0879 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0879 g| ≤ (upper0879 : ℝ) :=
  abs_of_coefficients coefficients0879 upper0879 powerCoefficients10 plusWeights0879 minusWeights0879
    checked0879.1 checked0879.2.1 checked0879.2.2.1 checked0879.2.2.2
    (power_identity10 plusWeights0879) (power_identity10 minusWeights0879) g hg hmax

def envelope0879 : Envelope := ⟨coefficients0879, upper0879, bound0879⟩

def coefficients0880 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/128), (9/512), (55/1024), (283/8192), (435/8192), (575/16384), (565/32768)]

def upper0880 : ℚ := (168903613/65536000000000)

def plusWeights0880 : Fin 11 → ℚ := ![(168903613/65536000000000), (168903613/6553600000000), (1520132517/13107200000000), (506710839/1638400000000), (3562335873/6553600000000), (10874207619/16384000000000), (3783487873/6553600000000), (586748499/1638400000000), (2008339317/13107200000000), (268306723/6553600000000), (168903613/32768000000000)]

def minusWeights0880 : Fin 11 → ℚ := ![(168903613/65536000000000), (168903613/6553600000000), (1520132517/13107200000000), (506710839/1638400000000), (3531615873/6553600000000), (10407647619/16384000000000), (3310463873/6553600000000), (426673179/1638400000000), (1031925717/13107200000000), (69500503/6553600000000), 0]

theorem checked0880 :
    (∀ i, 0 ≤ plusWeights0880 i) ∧
    (∀ i, 0 ≤ minusWeights0880 i) ∧
    (∀ i, plusCoefficients coefficients0880 upper0880 i = powerCoefficients10 plusWeights0880 i) ∧
    (∀ i, minusCoefficients coefficients0880 upper0880 i = powerCoefficients10 minusWeights0880 i) := by
  decide +kernel

theorem bound0880 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0880 g| ≤ (upper0880 : ℝ) :=
  abs_of_coefficients coefficients0880 upper0880 powerCoefficients10 plusWeights0880 minusWeights0880
    checked0880.1 checked0880.2.1 checked0880.2.2.1 checked0880.2.2.2
    (power_identity10 plusWeights0880) (power_identity10 minusWeights0880) g hg hmax

def envelope0880 : Envelope := ⟨coefficients0880, upper0880, bound0880⟩

def coefficients0881 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-13/256), (17/512), (271/4096), (3185/32768), (2745/65536), (8225/524288)]

def upper0881 : ℚ := (557427673/209715200000000)

def plusWeights0881 : Fin 11 → ℚ := ![(557427673/209715200000000), (557427673/20971520000000), (5016849057/41943040000000), (1672283019/5242880000000), (11771517133/20971520000000), (36074359399/52428800000000), (12636469453/20971520000000), (1974070027/5242880000000), (6779166177/41943040000000), (4503194277/104857600000000), (557427673/104857600000000)]

def minusWeights0881 : Fin 11 → ℚ := ![(557427673/209715200000000), (557427673/20971520000000), (5016849057/41943040000000), (1672283019/5242880000000), (11640445133/20971520000000), (34161527399/52428800000000), (10775492813/20971520000000), (1370496011/5242880000000), (3254531937/41943040000000), (1071082453/104857600000000), 0]

theorem checked0881 :
    (∀ i, 0 ≤ plusWeights0881 i) ∧
    (∀ i, 0 ≤ minusWeights0881 i) ∧
    (∀ i, plusCoefficients coefficients0881 upper0881 i = powerCoefficients10 plusWeights0881 i) ∧
    (∀ i, minusCoefficients coefficients0881 upper0881 i = powerCoefficients10 minusWeights0881 i) := by
  decide +kernel

theorem bound0881 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0881 g| ≤ (upper0881 : ℝ) :=
  abs_of_coefficients coefficients0881 upper0881 powerCoefficients10 plusWeights0881 minusWeights0881
    checked0881.1 checked0881.2.1 checked0881.2.2.1 checked0881.2.2.2
    (power_identity10 plusWeights0881) (power_identity10 minusWeights0881) g hg hmax

def envelope0881 : Envelope := ⟨coefficients0881, upper0881, bound0881⟩

def coefficients0882 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-19/512), (-49/1024), (-909/8192), (-393/4096), (-3633/65536), (-1981/131072)]

def upper0882 : ℚ := (3531003759/1310720000000000)

def plusWeights0882 : Fin 11 → ℚ := ![(3531003759/1310720000000000), (3531003759/131072000000000), (31779033831/262144000000000), (10593011277/32768000000000), (74560678939/131072000000000), (228475636817/327680000000000), (80045606939/131072000000000), (12512775677/32768000000000), (43009991911/262144000000000), (5715693773/131072000000000), (3531003759/655360000000000)]

def minusWeights0882 : Fin 11 → ℚ := ![(3531003759/1310720000000000), (3531003759/131072000000000), (31779033831/262144000000000), (10593011277/32768000000000), (73741478939/131072000000000), (216430836817/327680000000000), (68256550939/131072000000000), (8673246877/32768000000000), (20548075751/262144000000000), (269262749/26214400000000), 0]

theorem checked0882 :
    (∀ i, 0 ≤ plusWeights0882 i) ∧
    (∀ i, 0 ≤ minusWeights0882 i) ∧
    (∀ i, plusCoefficients coefficients0882 upper0882 i = powerCoefficients10 plusWeights0882 i) ∧
    (∀ i, minusCoefficients coefficients0882 upper0882 i = powerCoefficients10 minusWeights0882 i) := by
  decide +kernel

theorem bound0882 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0882 g| ≤ (upper0882 : ℝ) :=
  abs_of_coefficients coefficients0882 upper0882 powerCoefficients10 plusWeights0882 minusWeights0882
    checked0882.1 checked0882.2.1 checked0882.2.2.1 checked0882.2.2.2
    (power_identity10 plusWeights0882) (power_identity10 minusWeights0882) g hg hmax

def envelope0882 : Envelope := ⟨coefficients0882, upper0882, bound0882⟩

def coefficients0883 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-17/512), (-51/1024), (-761/8192), (-273/4096), (-1035/32768), (-525/65536)]

def upper0883 : ℚ := (71648559/26214400000000)

def plusWeights0883 : Fin 11 → ℚ := ![(71648559/26214400000000), (71648559/2621440000000), (644837031/5242880000000), (214945677/655360000000), (1512811739/2621440000000), (4634563217/6553600000000), (1623017179/2621440000000), (253593029/655360000000), (4357363523/26214400000000), (579248429/13107200000000), (71648559/13107200000000)]

def minusWeights0883 : Fin 11 → ℚ := ![(71648559/26214400000000), (71648559/2621440000000), (644837031/5242880000000), (214945677/655360000000), (1496427739/2621440000000), (4393155217/6553600000000), (1386222299/2621440000000), (7051933/26214400000), (2091006787/26214400000000), (137237161/13107200000000), 0]

theorem checked0883 :
    (∀ i, 0 ≤ plusWeights0883 i) ∧
    (∀ i, 0 ≤ minusWeights0883 i) ∧
    (∀ i, plusCoefficients coefficients0883 upper0883 i = powerCoefficients10 plusWeights0883 i) ∧
    (∀ i, minusCoefficients coefficients0883 upper0883 i = powerCoefficients10 minusWeights0883 i) := by
  decide +kernel

theorem bound0883 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0883 g| ≤ (upper0883 : ℝ) :=
  abs_of_coefficients coefficients0883 upper0883 powerCoefficients10 plusWeights0883 minusWeights0883
    checked0883.1 checked0883.2.1 checked0883.2.2.1 checked0883.2.2.2
    (power_identity10 plusWeights0883) (power_identity10 minusWeights0883) g hg hmax

def envelope0883 : Envelope := ⟨coefficients0883, upper0883, bound0883⟩

def coefficients0884 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-9/512), (-27/1024), (-575/8192), (-55/1024), (-1765/65536), (-925/131072)]

def upper0884 : ℚ := (152843991/52428800000000)

def plusWeights0884 : Fin 11 → ℚ := ![(152843991/52428800000000), (152843991/5242880000000), (1375595919/10485760000000), (458531973/1310720000000), (3226107811/5242880000000), (9872627433/13107200000000), (3450737571/5242880000000), (538000533/1310720000000), (1846798607/10485760000000), (1229354289/26214400000000), (152843991/26214400000000)]

def minusWeights0884 : Fin 11 → ℚ := ![(152843991/52428800000000), (152843991/5242880000000), (1375595919/10485760000000), (458531973/1310720000000), (3193339811/5242880000000), (9385715433/13107200000000), (2968710051/5242880000000), (379063413/1310720000000), (904393231/10485760000000), (299085621/26214400000000), 0]

theorem checked0884 :
    (∀ i, 0 ≤ plusWeights0884 i) ∧
    (∀ i, 0 ≤ minusWeights0884 i) ∧
    (∀ i, plusCoefficients coefficients0884 upper0884 i = powerCoefficients10 plusWeights0884 i) ∧
    (∀ i, minusCoefficients coefficients0884 upper0884 i = powerCoefficients10 minusWeights0884 i) := by
  decide +kernel

theorem bound0884 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0884 g| ≤ (upper0884 : ℝ) :=
  abs_of_coefficients coefficients0884 upper0884 powerCoefficients10 plusWeights0884 minusWeights0884
    checked0884.1 checked0884.2.1 checked0884.2.2.1 checked0884.2.2.2
    (power_identity10 plusWeights0884) (power_identity10 minusWeights0884) g hg hmax

def envelope0884 : Envelope := ⟨coefficients0884, upper0884, bound0884⟩

def coefficients0885 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (9/128), (37/512), (63/2048), (49/2048), (27/1024), (55/8192)]

def upper0885 : ℚ := (63958763/16384000000000)

def plusWeights0885 : Fin 11 → ℚ := ![(63958763/16384000000000), (63958763/1638400000000), (575628867/3276800000000), (191876289/409600000000), (1348254023/1638400000000), (4109082069/4096000000000), (1425812423/1638400000000), (220475949/409600000000), (753720691/3276800000000), (504641551/8192000000000), (63958763/8192000000000)]

def minusWeights0885 : Fin 11 → ℚ := ![(63958763/16384000000000), (63958763/1638400000000), (575628867/3276800000000), (191876289/409600000000), (1338014023/1638400000000), (3949722069/4096000000000), (1260455623/1638400000000), (163276629/409600000000), (397537043/3276800000000), (134946079/8192000000000), 0]

theorem checked0885 :
    (∀ i, 0 ≤ plusWeights0885 i) ∧
    (∀ i, 0 ≤ minusWeights0885 i) ∧
    (∀ i, plusCoefficients coefficients0885 upper0885 i = powerCoefficients10 plusWeights0885 i) ∧
    (∀ i, minusCoefficients coefficients0885 upper0885 i = powerCoefficients10 minusWeights0885 i) := by
  decide +kernel

theorem bound0885 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0885 g| ≤ (upper0885 : ℝ) :=
  abs_of_coefficients coefficients0885 upper0885 powerCoefficients10 plusWeights0885 minusWeights0885
    checked0885.1 checked0885.2.1 checked0885.2.2.1 checked0885.2.2.2
    (power_identity10 plusWeights0885) (power_identity10 minusWeights0885) g hg hmax

def envelope0885 : Envelope := ⟨coefficients0885, upper0885, bound0885⟩

def coefficients0886 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (23/256), (45/512), (227/4096), (171/4096), (141/4096), (135/16384)]

def upper0886 : ℚ := (26983287/6553600000000)

def plusWeights0886 : Fin 11 → ℚ := ![(26983287/6553600000000), (26983287/655360000000), (242849583/1310720000000), (80949861/163840000000), (568697027/655360000000), (1732139081/1638400000000), (600370627/655360000000), (92720369/163840000000), (1583895611/6553600000000), (1061428819/16384000000000), (26983287/3276800000000)]

def minusWeights0886 : Fin 11 → ℚ := ![(26983287/6553600000000), (26983287/655360000000), (242849583/1310720000000), (80949861/163840000000), (564601027/655360000000), (1667755081/1638400000000), (532927427/655360000000), (69179353/163840000000), (844600219/6553600000000), (287735531/16384000000000), 0]

theorem checked0886 :
    (∀ i, 0 ≤ plusWeights0886 i) ∧
    (∀ i, 0 ≤ minusWeights0886 i) ∧
    (∀ i, plusCoefficients coefficients0886 upper0886 i = powerCoefficients10 plusWeights0886 i) ∧
    (∀ i, minusCoefficients coefficients0886 upper0886 i = powerCoefficients10 minusWeights0886 i) := by
  decide +kernel

theorem bound0886 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0886 g| ≤ (upper0886 : ℝ) :=
  abs_of_coefficients coefficients0886 upper0886 powerCoefficients10 plusWeights0886 minusWeights0886
    checked0886.1 checked0886.2.1 checked0886.2.2.1 checked0886.2.2.2
    (power_identity10 plusWeights0886) (power_identity10 minusWeights0886) g hg hmax

def envelope0886 : Envelope := ⟨coefficients0886, upper0886, bound0886⟩

def coefficients0887 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/64), (13/512), (21/256), (509/8192), (849/8192), (1023/16384), (9275/262144)]

def upper0887 : ℚ := (2637563551/524288000000000)

def plusWeights0887 : Fin 11 → ℚ := ![(2637563551/524288000000000), (2637563551/52428800000000), (23738071959/104857600000000), (7912690653/13107200000000), (55634594571/52428800000000), (169886183713/131072000000000), (59146095371/52428800000000), (9179152893/13107200000000), (31430784791/104857600000000), (20984879883/262144000000000), (2637563551/262144000000000)]

def minusWeights0887 : Fin 11 → ℚ := ![(2637563551/524288000000000), (2637563551/52428800000000), (23738071959/104857600000000), (7912690653/13107200000000), (55143074571/52428800000000), (162446823713/131072000000000), (51631573771/52428800000000), (6646228413/13107200000000), (16045359127/104857600000000), (5390755627/262144000000000), 0]

theorem checked0887 :
    (∀ i, 0 ≤ plusWeights0887 i) ∧
    (∀ i, 0 ≤ minusWeights0887 i) ∧
    (∀ i, plusCoefficients coefficients0887 upper0887 i = powerCoefficients10 plusWeights0887 i) ∧
    (∀ i, minusCoefficients coefficients0887 upper0887 i = powerCoefficients10 minusWeights0887 i) := by
  decide +kernel

theorem bound0887 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0887 g| ≤ (upper0887 : ℝ) :=
  abs_of_coefficients coefficients0887 upper0887 powerCoefficients10 plusWeights0887 minusWeights0887
    checked0887.1 checked0887.2.1 checked0887.2.2.1 checked0887.2.2.2
    (power_identity10 plusWeights0887) (power_identity10 minusWeights0887) g hg hmax

def envelope0887 : Envelope := ⟨coefficients0887, upper0887, bound0887⟩

def coefficients0888 : Fin 11 → ℚ := ![0, 0, 0, 0, (7/128), (-5/128), (107/2048), (367/4096), (3657/32768), (3069/65536), (8545/524288)]

def upper0888 : ℚ := (5390200253/1048576000000000)

def plusWeights0888 : Fin 11 → ℚ := ![(5390200253/1048576000000000), (5390200253/104857600000000), (48511802277/209715200000000), (16170600759/26214400000000), (113767645313/104857600000000), (348081815939/262144000000000), (121596483713/104857600000000), (18941114039/26214400000000), (12993482849/41943040000000), (43255056857/524288000000000), (5390200253/524288000000000)]

def minusWeights0888 : Fin 11 → ℚ := ![(5390200253/1048576000000000), (5390200253/104857600000000), (48511802277/209715200000000), (16170600759/26214400000000), (112620765313/104857600000000), (331083415939/262144000000000), (104791926913/104857600000000), (13400087479/26214400000000), (32056190309/209715200000000), (10646945673/524288000000000), 0]

theorem checked0888 :
    (∀ i, 0 ≤ plusWeights0888 i) ∧
    (∀ i, 0 ≤ minusWeights0888 i) ∧
    (∀ i, plusCoefficients coefficients0888 upper0888 i = powerCoefficients10 plusWeights0888 i) ∧
    (∀ i, minusCoefficients coefficients0888 upper0888 i = powerCoefficients10 minusWeights0888 i) := by
  decide +kernel

theorem bound0888 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0888 g| ≤ (upper0888 : ℝ) :=
  abs_of_coefficients coefficients0888 upper0888 powerCoefficients10 plusWeights0888 minusWeights0888
    checked0888.1 checked0888.2.1 checked0888.2.2.1 checked0888.2.2.2
    (power_identity10 plusWeights0888) (power_identity10 minusWeights0888) g hg hmax

def envelope0888 : Envelope := ⟨coefficients0888, upper0888, bound0888⟩

def coefficients0889 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/16), (31/256), (55/512), (139/4096), (43/1024), (53/1024), (55/4096)]

def upper0889 : ℚ := (2481267/327680000000)

def plusWeights0889 : Fin 11 → ℚ := ![(2481267/327680000000), (2481267/32768000000), (22331403/65536000000), (7443801/8192000000), (52311407/32768000000), (159491021/81920000000), (55380527/32768000000), (5356593/5120000000), (732798443/1638400000000), (490363727/4096000000000), (2481267/163840000000)]

def minusWeights0889 : Fin 11 → ℚ := ![(2481267/327680000000), (2481267/32768000000), (22331403/65536000000), (7443801/8192000000), (51901807/32768000000), (153148621/81920000000), (48832687/32768000000), (15792633/20480000000), (383771707/1638400000000), (129953023/4096000000000), 0]

theorem checked0889 :
    (∀ i, 0 ≤ plusWeights0889 i) ∧
    (∀ i, 0 ≤ minusWeights0889 i) ∧
    (∀ i, plusCoefficients coefficients0889 upper0889 i = powerCoefficients10 plusWeights0889 i) ∧
    (∀ i, minusCoefficients coefficients0889 upper0889 i = powerCoefficients10 minusWeights0889 i) := by
  decide +kernel

theorem bound0889 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0889 g| ≤ (upper0889 : ℝ) :=
  abs_of_coefficients coefficients0889 upper0889 powerCoefficients10 plusWeights0889 minusWeights0889
    checked0889.1 checked0889.2.1 checked0889.2.2.1 checked0889.2.2.2
    (power_identity10 plusWeights0889) (power_identity10 minusWeights0889) g hg hmax

def envelope0889 : Envelope := ⟨coefficients0889, upper0889, bound0889⟩

def coefficients0890 : Fin 11 → ℚ := ![0, 0, 0, (1/32), (1/8), (23/128), (157/1024), (691/8192), (189/4096), (9/256), (135/16384)]

def upper0890 : ℚ := (1497796699/32768000000000)

def plusWeights0890 : Fin 11 → ℚ := ![(1497796699/32768000000000), (1497796699/3276800000000), (13480170291/6553600000000), (4518990097/819200000000), (32211490679/3276800000000), (100366312037/8192000000000), (35682073079/3276800000000), (5609419407/819200000000), (3826745591/1310720000000), (12459461791/16384000000000), (1497796699/16384000000000)]

def minusWeights0890 : Fin 11 → ℚ := ![(1497796699/32768000000000), (1497796699/3276800000000), (13480170291/6553600000000), (4467790097/819200000000), (30695970679/3276800000000), (88356072037/8192000000000), (27225388279/3276800000000), (3377360787/819200000000), (7826612627/6553600000000), (2518505199/16384000000000), 0]

theorem checked0890 :
    (∀ i, 0 ≤ plusWeights0890 i) ∧
    (∀ i, 0 ≤ minusWeights0890 i) ∧
    (∀ i, plusCoefficients coefficients0890 upper0890 i = powerCoefficients10 plusWeights0890 i) ∧
    (∀ i, minusCoefficients coefficients0890 upper0890 i = powerCoefficients10 minusWeights0890 i) := by
  decide +kernel

theorem bound0890 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0890 g| ≤ (upper0890 : ℝ) :=
  abs_of_coefficients coefficients0890 upper0890 powerCoefficients10 plusWeights0890 minusWeights0890
    checked0890.1 checked0890.2.1 checked0890.2.2.1 checked0890.2.2.2
    (power_identity10 plusWeights0890) (power_identity10 minusWeights0890) g hg hmax

def envelope0890 : Envelope := ⟨coefficients0890, upper0890, bound0890⟩

def coefficients0891 : Fin 11 → ℚ := ![0, 0, 0, (1/32), (5/32), (27/128), (39/256), (383/8192), (41/2048), (61/2048), (65/8192)]

def upper0891 : ℚ := (805136381/16384000000000)

def plusWeights0891 : Fin 11 → ℚ := ![(805136381/16384000000000), (805136381/1638400000000), (7246227429/3276800000000), (2428209143/409600000000), (17291864001/1638400000000), (53804232003/4096000000000), (19101393601/1638400000000), (1500150329/204800000000), (2047357849/655360000000), (6677192329/8192000000000), (805136381/8192000000000)]

def minusWeights0891 : Fin 11 → ℚ := ![(805136381/16384000000000), (805136381/1638400000000), (7246227429/3276800000000), (2402609143/409600000000), (16523864001/1638400000000), (47642952003/4096000000000), (14714334401/1638400000000), (457629407/102400000000), (4255665613/3276800000000), (1374171481/8192000000000), 0]

theorem checked0891 :
    (∀ i, 0 ≤ plusWeights0891 i) ∧
    (∀ i, 0 ≤ minusWeights0891 i) ∧
    (∀ i, plusCoefficients coefficients0891 upper0891 i = powerCoefficients10 plusWeights0891 i) ∧
    (∀ i, minusCoefficients coefficients0891 upper0891 i = powerCoefficients10 minusWeights0891 i) := by
  decide +kernel

theorem bound0891 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0891 g| ≤ (upper0891 : ℝ) :=
  abs_of_coefficients coefficients0891 upper0891 powerCoefficients10 plusWeights0891 minusWeights0891
    checked0891.1 checked0891.2.1 checked0891.2.2.1 checked0891.2.2.2
    (power_identity10 plusWeights0891) (power_identity10 minusWeights0891) g hg hmax

def envelope0891 : Envelope := ⟨coefficients0891, upper0891, bound0891⟩

end BilayerDressed.CubicQuarticEnvelopes

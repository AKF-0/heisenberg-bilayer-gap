import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0416 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/512), (119/4096), (13/1024), (21/2048), (5/2048)]

def upper0416 : ℚ := (68463/4096000000000)

def plusWeights0416 : Fin 11 → ℚ := ![(68463/4096000000000), (68463/409600000000), (616167/819200000000), (205389/102400000000), (1437723/409600000000), (4313169/1024000000000), (1443323/409600000000), (422573/204800000000), (690611/819200000000), (236353/1024000000000), (68463/2048000000000)]

def minusWeights0416 : Fin 11 → ℚ := ![(68463/4096000000000), (68463/409600000000), (616167/819200000000), (205389/102400000000), (1437723/409600000000), (4313169/1024000000000), (1432123/409600000000), (398983/204800000000), (541723/819200000000), (52981/512000000000), 0]

theorem checked0416 :
    (∀ i, 0 ≤ plusWeights0416 i) ∧
    (∀ i, 0 ≤ minusWeights0416 i) ∧
    (∀ i, plusCoefficients coefficients0416 upper0416 i = powerCoefficients10 plusWeights0416 i) ∧
    (∀ i, minusCoefficients coefficients0416 upper0416 i = powerCoefficients10 minusWeights0416 i) := by
  decide +kernel

theorem bound0416 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0416 g| ≤ (upper0416 : ℝ) :=
  abs_of_coefficients coefficients0416 upper0416 powerCoefficients10 plusWeights0416 minusWeights0416
    checked0416.1 checked0416.2.1 checked0416.2.2.1 checked0416.2.2.2
    (power_identity10 plusWeights0416) (power_identity10 minusWeights0416) g hg hmax

def envelope0416 : Envelope := ⟨coefficients0416, upper0416, bound0416⟩

def coefficients0417 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/512), (119/4096), (29/512), (111/2048), (55/4096)]

def upper0417 : ℚ := (28179/1638400000000)

def plusWeights0417 : Fin 11 → ℚ := ![(28179/1638400000000), (28179/163840000000), (253611/327680000000), (84537/40960000000), (591759/163840000000), (1775277/409600000000), (593999/163840000000), (5431/2560000000), (1417663/1638400000000), (969037/4096000000000), (28179/819200000000)]

def minusWeights0417 : Fin 11 → ℚ := ![(28179/1638400000000), (28179/163840000000), (253611/327680000000), (84537/40960000000), (591759/163840000000), (1775277/409600000000), (589519/163840000000), (41089/20480000000), (1118447/1638400000000), (439913/4096000000000), 0]

theorem checked0417 :
    (∀ i, 0 ≤ plusWeights0417 i) ∧
    (∀ i, 0 ≤ minusWeights0417 i) ∧
    (∀ i, plusCoefficients coefficients0417 upper0417 i = powerCoefficients10 plusWeights0417 i) ∧
    (∀ i, minusCoefficients coefficients0417 upper0417 i = powerCoefficients10 minusWeights0417 i) := by
  decide +kernel

theorem bound0417 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0417 g| ≤ (upper0417 : ℝ) :=
  abs_of_coefficients coefficients0417 upper0417 powerCoefficients10 plusWeights0417 minusWeights0417
    checked0417.1 checked0417.2.1 checked0417.2.2.1 checked0417.2.2.2
    (power_identity10 plusWeights0417) (power_identity10 minusWeights0417) g hg hmax

def envelope0417 : Envelope := ⟨coefficients0417, upper0417, bound0417⟩

def coefficients0418 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (-159/4096), (-201/4096), (-2649/32768), (-2223/65536)]

def upper0418 : ℚ := (6679197/655360000000000)

def plusWeights0418 : Fin 11 → ℚ := ![(6679197/655360000000000), (6679197/65536000000000), (60112773/131072000000000), (20037591/16384000000000), (140263137/65536000000000), (420789411/163840000000000), (141223137/65536000000000), (20933991/16384000000000), (70042053/131072000000000), (9686379/65536000000000), (6679197/327680000000000)]

def minusWeights0418 : Fin 11 → ℚ := ![(6679197/655360000000000), (6679197/65536000000000), (60112773/131072000000000), (20037591/16384000000000), (140263137/65536000000000), (420789411/163840000000000), (139303137/65536000000000), (19141191/16384000000000), (50183493/131072000000000), (734403/13107200000000), 0]

theorem checked0418 :
    (∀ i, 0 ≤ plusWeights0418 i) ∧
    (∀ i, 0 ≤ minusWeights0418 i) ∧
    (∀ i, plusCoefficients coefficients0418 upper0418 i = powerCoefficients10 plusWeights0418 i) ∧
    (∀ i, minusCoefficients coefficients0418 upper0418 i = powerCoefficients10 minusWeights0418 i) := by
  decide +kernel

theorem bound0418 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0418 g| ≤ (upper0418 : ℝ) :=
  abs_of_coefficients coefficients0418 upper0418 powerCoefficients10 plusWeights0418 minusWeights0418
    checked0418.1 checked0418.2.1 checked0418.2.2.1 checked0418.2.2.2
    (power_identity10 plusWeights0418) (power_identity10 minusWeights0418) g hg hmax

def envelope0418 : Envelope := ⟨coefficients0418, upper0418, bound0418⟩

def coefficients0419 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (-105/4096), (-135/4096), (-945/32768), (-675/65536)]

def upper0419 : ℚ := (307377/26214400000000)

def plusWeights0419 : Fin 11 → ℚ := ![(307377/26214400000000), (307377/2621440000000), (2766393/5242880000000), (922131/655360000000), (6454917/2621440000000), (19364751/6553600000000), (6493317/2621440000000), (958851/655360000000), (637029/1048576000000), (2195067/13107200000000), (307377/13107200000000)]

def minusWeights0419 : Fin 11 → ℚ := ![(307377/26214400000000), (307377/2621440000000), (2766393/5242880000000), (922131/655360000000), (6454917/2621440000000), (19364751/6553600000000), (6416517/2621440000000), (885411/655360000000), (2347641/5242880000000), (878703/13107200000000), 0]

theorem checked0419 :
    (∀ i, 0 ≤ plusWeights0419 i) ∧
    (∀ i, 0 ≤ minusWeights0419 i) ∧
    (∀ i, plusCoefficients coefficients0419 upper0419 i = powerCoefficients10 plusWeights0419 i) ∧
    (∀ i, minusCoefficients coefficients0419 upper0419 i = powerCoefficients10 minusWeights0419 i) := by
  decide +kernel

theorem bound0419 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0419 g| ≤ (upper0419 : ℝ) :=
  abs_of_coefficients coefficients0419 upper0419 powerCoefficients10 plusWeights0419 minusWeights0419
    checked0419.1 checked0419.2.1 checked0419.2.2.1 checked0419.2.2.2
    (power_identity10 plusWeights0419) (power_identity10 minusWeights0419) g hg hmax

def envelope0419 : Envelope := ⟨coefficients0419, upper0419, bound0419⟩

def coefficients0420 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (-5/4096), (-35/4096), (-315/65536), (-175/131072)]

def upper0420 : ℚ := (756861/52428800000000)

def plusWeights0420 : Fin 11 → ℚ := ![(756861/52428800000000), (756861/5242880000000), (6811749/10485760000000), (2270583/1310720000000), (15894081/5242880000000), (47682243/13107200000000), (15970881/5242880000000), (2347223/1310720000000), (7728613/10485760000000), (5306099/26214400000000), (756861/26214400000000)]

def minusWeights0420 : Fin 11 → ℚ := ![(756861/52428800000000), (756861/5242880000000), (6811749/10485760000000), (2270583/1310720000000), (15894081/5242880000000), (47682243/13107200000000), (15817281/5242880000000), (2193943/1310720000000), (1178977/2097152000000), (2262511/26214400000000), 0]

theorem checked0420 :
    (∀ i, 0 ≤ plusWeights0420 i) ∧
    (∀ i, 0 ≤ minusWeights0420 i) ∧
    (∀ i, plusCoefficients coefficients0420 upper0420 i = powerCoefficients10 plusWeights0420 i) ∧
    (∀ i, minusCoefficients coefficients0420 upper0420 i = powerCoefficients10 minusWeights0420 i) := by
  decide +kernel

theorem bound0420 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0420 g| ≤ (upper0420 : ℝ) :=
  abs_of_coefficients coefficients0420 upper0420 powerCoefficients10 plusWeights0420 minusWeights0420
    checked0420.1 checked0420.2.1 checked0420.2.2.1 checked0420.2.2.2
    (power_identity10 plusWeights0420) (power_identity10 minusWeights0420) g hg hmax

def envelope0420 : Envelope := ⟨coefficients0420, upper0420, bound0420⟩

def coefficients0421 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (55/8192), (5/1024), (45/4096), (25/8192)]

def upper0421 : ℚ := (50397/3276800000000)

def plusWeights0421 : Fin 11 → ℚ := ![(50397/3276800000000), (50397/327680000000), (453573/655360000000), (151191/81920000000), (1058337/327680000000), (3175011/819200000000), (1063137/327680000000), (78023/40960000000), (20501/26214400000), (351463/1638400000000), (50397/1638400000000)]

def minusWeights0421 : Fin 11 → ℚ := ![(50397/3276800000000), (50397/327680000000), (453573/655360000000), (151191/81920000000), (1058337/327680000000), (3175011/819200000000), (1053537/327680000000), (4573/2560000000), (394621/655360000000), (152507/1638400000000), 0]

theorem checked0421 :
    (∀ i, 0 ≤ plusWeights0421 i) ∧
    (∀ i, 0 ≤ minusWeights0421 i) ∧
    (∀ i, plusCoefficients coefficients0421 upper0421 i = powerCoefficients10 plusWeights0421 i) ∧
    (∀ i, minusCoefficients coefficients0421 upper0421 i = powerCoefficients10 minusWeights0421 i) := by
  decide +kernel

theorem bound0421 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0421 g| ≤ (upper0421 : ℝ) :=
  abs_of_coefficients coefficients0421 upper0421 powerCoefficients10 plusWeights0421 minusWeights0421
    checked0421.1 checked0421.2.1 checked0421.2.2.1 checked0421.2.2.2
    (power_identity10 plusWeights0421) (power_identity10 minusWeights0421) g hg hmax

def envelope0421 : Envelope := ⟨coefficients0421, upper0421, bound0421⟩

def coefficients0422 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (5/512), (15/2048), (25/4096), (275/262144)]

def upper0422 : ℚ := (1646731/104857600000000)

def plusWeights0422 : Fin 11 → ℚ := ![(1646731/104857600000000), (1646731/10485760000000), (14820579/20971520000000), (4940193/2621440000000), (34581351/10485760000000), (103744053/26214400000000), (34734951/10485760000000), (5096353/2621440000000), (3345351/4194304000000), (2293451/10485760000000), (1646731/52428800000000)]

def minusWeights0422 : Fin 11 → ℚ := ![(1646731/104857600000000), (1646731/10485760000000), (14820579/20971520000000), (4940193/2621440000000), (34581351/10485760000000), (103744053/26214400000000), (34427751/10485760000000), (4784033/2621440000000), (12914403/20971520000000), (1000011/10485760000000), 0]

theorem checked0422 :
    (∀ i, 0 ≤ plusWeights0422 i) ∧
    (∀ i, 0 ≤ minusWeights0422 i) ∧
    (∀ i, plusCoefficients coefficients0422 upper0422 i = powerCoefficients10 plusWeights0422 i) ∧
    (∀ i, minusCoefficients coefficients0422 upper0422 i = powerCoefficients10 minusWeights0422 i) := by
  decide +kernel

theorem bound0422 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0422 g| ≤ (upper0422 : ℝ) :=
  abs_of_coefficients coefficients0422 upper0422 powerCoefficients10 plusWeights0422 minusWeights0422
    checked0422.1 checked0422.2.1 checked0422.2.2.1 checked0422.2.2.2
    (power_identity10 plusWeights0422) (power_identity10 minusWeights0422) g hg hmax

def envelope0422 : Envelope := ⟨coefficients0422, upper0422, bound0422⟩

def coefficients0423 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (5/512), (265/16384), (365/32768), (615/131072)]

def upper0423 : ℚ := (4141443/262144000000000)

def plusWeights0423 : Fin 11 → ℚ := ![(4141443/262144000000000), (4141443/26214400000000), (37272987/52428800000000), (12424329/6553600000000), (86970303/26214400000000), (260910909/65536000000000), (87354303/26214400000000), (12814729/6553600000000), (42043067/52428800000000), (1152603/5242880000000), (4141443/131072000000000)]

def minusWeights0423 : Fin 11 → ℚ := ![(4141443/262144000000000), (4141443/26214400000000), (37272987/52428800000000), (12424329/6553600000000), (86970303/26214400000000), (260910909/65536000000000), (86586303/26214400000000), (12033929/6553600000000), (32502907/52428800000000), (2519871/26214400000000), 0]

theorem checked0423 :
    (∀ i, 0 ≤ plusWeights0423 i) ∧
    (∀ i, 0 ≤ minusWeights0423 i) ∧
    (∀ i, plusCoefficients coefficients0423 upper0423 i = powerCoefficients10 plusWeights0423 i) ∧
    (∀ i, minusCoefficients coefficients0423 upper0423 i = powerCoefficients10 minusWeights0423 i) := by
  decide +kernel

theorem bound0423 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0423 g| ≤ (upper0423 : ℝ) :=
  abs_of_coefficients coefficients0423 upper0423 powerCoefficients10 plusWeights0423 minusWeights0423
    checked0423.1 checked0423.2.1 checked0423.2.2.1 checked0423.2.2.2
    (power_identity10 plusWeights0423) (power_identity10 minusWeights0423) g hg hmax

def envelope0423 : Envelope := ⟨coefficients0423, upper0423, bound0423⟩

def coefficients0424 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (5/512), (135/8192), (175/16384), (1025/262144)]

def upper0424 : ℚ := (1656841/104857600000000)

def plusWeights0424 : Fin 11 → ℚ := ![(1656841/104857600000000), (1656841/10485760000000), (14911569/20971520000000), (4970523/2621440000000), (34793661/10485760000000), (104380983/26214400000000), (34947261/10485760000000), (5126683/2621440000000), (3363933/4194304000000), (2305529/10485760000000), (1656841/52428800000000)]

def minusWeights0424 : Fin 11 → ℚ := ![(1656841/104857600000000), (1656841/10485760000000), (14911569/20971520000000), (4970523/2621440000000), (34793661/10485760000000), (104380983/26214400000000), (34640061/10485760000000), (4814363/2621440000000), (13003473/20971520000000), (1008153/10485760000000), 0]

theorem checked0424 :
    (∀ i, 0 ≤ plusWeights0424 i) ∧
    (∀ i, 0 ≤ minusWeights0424 i) ∧
    (∀ i, plusCoefficients coefficients0424 upper0424 i = powerCoefficients10 plusWeights0424 i) ∧
    (∀ i, minusCoefficients coefficients0424 upper0424 i = powerCoefficients10 minusWeights0424 i) := by
  decide +kernel

theorem bound0424 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0424 g| ≤ (upper0424 : ℝ) :=
  abs_of_coefficients coefficients0424 upper0424 powerCoefficients10 plusWeights0424 minusWeights0424
    checked0424.1 checked0424.2.1 checked0424.2.2.1 checked0424.2.2.2
    (power_identity10 plusWeights0424) (power_identity10 minusWeights0424) g hg hmax

def envelope0424 : Envelope := ⟨coefficients0424, upper0424, bound0424⟩

def coefficients0425 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (5/512), (1175/32768), (1695/65536), (16865/524288)]

def upper0425 : ℚ := (16790493/1048576000000000)

def plusWeights0425 : Fin 11 → ℚ := ![(16790493/1048576000000000), (16790493/104857600000000), (151114437/209715200000000), (50371479/26214400000000), (352600353/104857600000000), (1057801059/262144000000000), (354136353/104857600000000), (51933079/26214400000000), (170236037/209715200000000), (4663921/20971520000000), (16790493/524288000000000)]

def minusWeights0425 : Fin 11 → ℚ := ![(16790493/1048576000000000), (16790493/104857600000000), (151114437/209715200000000), (50371479/26214400000000), (352600353/104857600000000), (1057801059/262144000000000), (351064353/104857600000000), (48809879/26214400000000), (131992837/209715200000000), (10261381/104857600000000), 0]

theorem checked0425 :
    (∀ i, 0 ≤ plusWeights0425 i) ∧
    (∀ i, 0 ≤ minusWeights0425 i) ∧
    (∀ i, plusCoefficients coefficients0425 upper0425 i = powerCoefficients10 plusWeights0425 i) ∧
    (∀ i, minusCoefficients coefficients0425 upper0425 i = powerCoefficients10 minusWeights0425 i) := by
  decide +kernel

theorem bound0425 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0425 g| ≤ (upper0425 : ℝ) :=
  abs_of_coefficients coefficients0425 upper0425 powerCoefficients10 plusWeights0425 minusWeights0425
    checked0425.1 checked0425.2.1 checked0425.2.2.1 checked0425.2.2.2
    (power_identity10 plusWeights0425) (power_identity10 minusWeights0425) g hg hmax

def envelope0425 : Envelope := ⟨coefficients0425, upper0425, bound0425⟩

def coefficients0426 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/1024), (5/512), (1075/16384), (1535/32768), (2115/32768)]

def upper0426 : ℚ := (1070493/65536000000000)

def plusWeights0426 : Fin 11 → ℚ := ![(1070493/65536000000000), (1070493/6553600000000), (9634437/13107200000000), (3211479/1638400000000), (22480353/6553600000000), (67441059/16384000000000), (22576353/6553600000000), (3309079/1638400000000), (10833437/13107200000000), (7413/32768000000), (1070493/32768000000000)]

def minusWeights0426 : Fin 11 → ℚ := ![(1070493/65536000000000), (1070493/6553600000000), (9634437/13107200000000), (3211479/1638400000000), (22480353/6553600000000), (67441059/16384000000000), (22384353/6553600000000), (3113879/1638400000000), (8435437/13107200000000), (329193/3276800000000), 0]

theorem checked0426 :
    (∀ i, 0 ≤ plusWeights0426 i) ∧
    (∀ i, 0 ≤ minusWeights0426 i) ∧
    (∀ i, plusCoefficients coefficients0426 upper0426 i = powerCoefficients10 plusWeights0426 i) ∧
    (∀ i, minusCoefficients coefficients0426 upper0426 i = powerCoefficients10 minusWeights0426 i) := by
  decide +kernel

theorem bound0426 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0426 g| ≤ (upper0426 : ℝ) :=
  abs_of_coefficients coefficients0426 upper0426 powerCoefficients10 plusWeights0426 minusWeights0426
    checked0426.1 checked0426.2.1 checked0426.2.2.1 checked0426.2.2.2
    (power_identity10 plusWeights0426) (power_identity10 minusWeights0426) g hg hmax

def envelope0426 : Envelope := ⟨coefficients0426, upper0426, bound0426⟩

def coefficients0427 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/64), (3/128), (47/1024), (37/1024), (35/4096)]

def upper0427 : ℚ := (151263/8192000000000)

def plusWeights0427 : Fin 11 → ℚ := ![(151263/8192000000000), (151263/819200000000), (1361367/1638400000000), (453789/204800000000), (3176523/819200000000), (9529569/2048000000000), (3189323/819200000000), (467069/204800000000), (1527239/1638400000000), (1045023/4096000000000), (151263/4096000000000)]

def minusWeights0427 : Fin 11 → ℚ := ![(151263/8192000000000), (151263/819200000000), (1361367/1638400000000), (453789/204800000000), (3176523/819200000000), (9529569/2048000000000), (3163723/819200000000), (440509/204800000000), (239099/327680000000), (467607/4096000000000), 0]

theorem checked0427 :
    (∀ i, 0 ≤ plusWeights0427 i) ∧
    (∀ i, 0 ≤ minusWeights0427 i) ∧
    (∀ i, plusCoefficients coefficients0427 upper0427 i = powerCoefficients10 plusWeights0427 i) ∧
    (∀ i, minusCoefficients coefficients0427 upper0427 i = powerCoefficients10 minusWeights0427 i) := by
  decide +kernel

theorem bound0427 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0427 g| ≤ (upper0427 : ℝ) :=
  abs_of_coefficients coefficients0427 upper0427 powerCoefficients10 plusWeights0427 minusWeights0427
    checked0427.1 checked0427.2.1 checked0427.2.2.1 checked0427.2.2.2
    (power_identity10 plusWeights0427) (power_identity10 minusWeights0427) g hg hmax

def envelope0427 : Envelope := ⟨coefficients0427, upper0427, bound0427⟩

def coefficients0428 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/64), (3/128), (57/1024), (47/1024), (45/4096)]

def upper0428 : ℚ := (30429/1638400000000)

def plusWeights0428 : Fin 11 → ℚ := ![(30429/1638400000000), (30429/163840000000), (273861/327680000000), (91287/40960000000), (639009/163840000000), (1917027/409600000000), (641569/163840000000), (93943/40960000000), (1535337/1638400000000), (1050273/4096000000000), (30429/819200000000)]

def minusWeights0428 : Fin 11 → ℚ := ![(30429/1638400000000), (30429/163840000000), (273861/327680000000), (91287/40960000000), (639009/163840000000), (1917027/409600000000), (636449/163840000000), (88631/40960000000), (1203273/1638400000000), (471177/4096000000000), 0]

theorem checked0428 :
    (∀ i, 0 ≤ plusWeights0428 i) ∧
    (∀ i, 0 ≤ minusWeights0428 i) ∧
    (∀ i, plusCoefficients coefficients0428 upper0428 i = powerCoefficients10 plusWeights0428 i) ∧
    (∀ i, minusCoefficients coefficients0428 upper0428 i = powerCoefficients10 minusWeights0428 i) := by
  decide +kernel

theorem bound0428 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0428 g| ≤ (upper0428 : ℝ) :=
  abs_of_coefficients coefficients0428 upper0428 powerCoefficients10 plusWeights0428 minusWeights0428
    checked0428.1 checked0428.2.1 checked0428.2.2.1 checked0428.2.2.2
    (power_identity10 plusWeights0428) (power_identity10 minusWeights0428) g hg hmax

def envelope0428 : Envelope := ⟨coefficients0428, upper0428, bound0428⟩

def coefficients0429 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/64), (3/128), (31/512), (13/256), (25/2048)]

def upper0429 : ℚ := (76293/4096000000000)

def plusWeights0429 : Fin 11 → ℚ := ![(76293/4096000000000), (76293/409600000000), (686637/819200000000), (228879/102400000000), (1602153/409600000000), (4806459/1024000000000), (1608553/409600000000), (235519/102400000000), (769693/819200000000), (526449/2048000000000), (76293/2048000000000)]

def minusWeights0429 : Fin 11 → ℚ := ![(76293/4096000000000), (76293/409600000000), (686637/819200000000), (228879/102400000000), (1602153/409600000000), (4806459/1024000000000), (1595753/409600000000), (222239/102400000000), (603581/819200000000), (236481/2048000000000), 0]

theorem checked0429 :
    (∀ i, 0 ≤ plusWeights0429 i) ∧
    (∀ i, 0 ≤ minusWeights0429 i) ∧
    (∀ i, plusCoefficients coefficients0429 upper0429 i = powerCoefficients10 plusWeights0429 i) ∧
    (∀ i, minusCoefficients coefficients0429 upper0429 i = powerCoefficients10 minusWeights0429 i) := by
  decide +kernel

theorem bound0429 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0429 g| ≤ (upper0429 : ℝ) :=
  abs_of_coefficients coefficients0429 upper0429 powerCoefficients10 plusWeights0429 minusWeights0429
    checked0429.1 checked0429.2.1 checked0429.2.2.1 checked0429.2.2.2
    (power_identity10 plusWeights0429) (power_identity10 minusWeights0429) g hg hmax

def envelope0429 : Envelope := ⟨coefficients0429, upper0429, bound0429⟩

def coefficients0430 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/64), (3/128), (77/1024), (67/1024), (65/4096)]

def upper0430 : ℚ := (153909/8192000000000)

def plusWeights0430 : Fin 11 → ℚ := ![(153909/8192000000000), (153909/819200000000), (1385181/1638400000000), (461727/204800000000), (3232089/819200000000), (9696267/2048000000000), (3244889/819200000000), (475007/204800000000), (1551533/1638400000000), (1060773/4096000000000), (153909/4096000000000)]

def minusWeights0430 : Fin 11 → ℚ := ![(153909/8192000000000), (153909/819200000000), (1385181/1638400000000), (461727/204800000000), (3232089/819200000000), (9696267/2048000000000), (3219289/819200000000), (448447/204800000000), (1218829/1638400000000), (478317/4096000000000), 0]

theorem checked0430 :
    (∀ i, 0 ≤ plusWeights0430 i) ∧
    (∀ i, 0 ≤ minusWeights0430 i) ∧
    (∀ i, plusCoefficients coefficients0430 upper0430 i = powerCoefficients10 plusWeights0430 i) ∧
    (∀ i, minusCoefficients coefficients0430 upper0430 i = powerCoefficients10 minusWeights0430 i) := by
  decide +kernel

theorem bound0430 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0430 g| ≤ (upper0430 : ℝ) :=
  abs_of_coefficients coefficients0430 upper0430 powerCoefficients10 plusWeights0430 minusWeights0430
    checked0430.1 checked0430.2.1 checked0430.2.2.1 checked0430.2.2.2
    (power_identity10 plusWeights0430) (power_identity10 minusWeights0430) g hg hmax

def envelope0430 : Envelope := ⟨coefficients0430, upper0430, bound0430⟩

def coefficients0431 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/64), (3/128), (41/512), (9/128), (35/2048)]

def upper0431 : ℚ := (3087/163840000000)

def plusWeights0431 : Fin 11 → ℚ := ![(3087/163840000000), (3087/16384000000), (27783/32768000000), (9261/4096000000), (64827/16384000000), (194481/40960000000), (65083/16384000000), (47633/20480000000), (777791/819200000000), (531699/2048000000000), (3087/81920000000)]

def minusWeights0431 : Fin 11 → ℚ := ![(3087/163840000000), (3087/16384000000), (27783/32768000000), (9261/4096000000), (64827/16384000000), (194481/40960000000), (64571/16384000000), (44977/20480000000), (611359/819200000000), (240051/2048000000000), 0]

theorem checked0431 :
    (∀ i, 0 ≤ plusWeights0431 i) ∧
    (∀ i, 0 ≤ minusWeights0431 i) ∧
    (∀ i, plusCoefficients coefficients0431 upper0431 i = powerCoefficients10 plusWeights0431 i) ∧
    (∀ i, minusCoefficients coefficients0431 upper0431 i = powerCoefficients10 minusWeights0431 i) := by
  decide +kernel

theorem bound0431 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0431 g| ≤ (upper0431 : ℝ) :=
  abs_of_coefficients coefficients0431 upper0431 powerCoefficients10 plusWeights0431 minusWeights0431
    checked0431.1 checked0431.2.1 checked0431.2.2.1 checked0431.2.2.2
    (power_identity10 plusWeights0431) (power_identity10 minusWeights0431) g hg hmax

def envelope0431 : Envelope := ⟨coefficients0431, upper0431, bound0431⟩

def coefficients0432 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (1/64), (3/128), (87/1024), (77/1024), (75/4096)]

def upper0432 : ℚ := (154791/8192000000000)

def plusWeights0432 : Fin 11 → ℚ := ![(154791/8192000000000), (154791/819200000000), (1393119/1638400000000), (464373/204800000000), (3250611/819200000000), (9751833/2048000000000), (3263411/819200000000), (477653/204800000000), (1559631/1638400000000), (1066023/4096000000000), (154791/4096000000000)]

def minusWeights0432 : Fin 11 → ℚ := ![(154791/8192000000000), (154791/819200000000), (1393119/1638400000000), (464373/204800000000), (3250611/819200000000), (9751833/2048000000000), (3237811/819200000000), (451093/204800000000), (1226607/1638400000000), (481887/4096000000000), 0]

theorem checked0432 :
    (∀ i, 0 ≤ plusWeights0432 i) ∧
    (∀ i, 0 ≤ minusWeights0432 i) ∧
    (∀ i, plusCoefficients coefficients0432 upper0432 i = powerCoefficients10 plusWeights0432 i) ∧
    (∀ i, minusCoefficients coefficients0432 upper0432 i = powerCoefficients10 minusWeights0432 i) := by
  decide +kernel

theorem bound0432 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0432 g| ≤ (upper0432 : ℝ) :=
  abs_of_coefficients coefficients0432 upper0432 powerCoefficients10 plusWeights0432 minusWeights0432
    checked0432.1 checked0432.2.1 checked0432.2.2.1 checked0432.2.2.2
    (power_identity10 plusWeights0432) (power_identity10 minusWeights0432) g hg hmax

def envelope0432 : Envelope := ⟨coefficients0432, upper0432, bound0432⟩

def coefficients0433 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (35/2048), (5/2048), (725/32768), (1425/65536), (2075/262144)]

def upper0433 : ℚ := (1843163/104857600000000)

def plusWeights0433 : Fin 11 → ℚ := ![(1843163/104857600000000), (1843163/10485760000000), (16588467/20971520000000), (5529489/2621440000000), (38706423/10485760000000), (116119269/26214400000000), (38885623/10485760000000), (5709329/2621440000000), (18758867/20971520000000), (2572511/10485760000000), (1843163/52428800000000)]

def minusWeights0433 : Fin 11 → ℚ := ![(1843163/104857600000000), (1843163/10485760000000), (16588467/20971520000000), (5529489/2621440000000), (38706423/10485760000000), (116119269/26214400000000), (38527223/10485760000000), (5349649/2621440000000), (14418067/20971520000000), (222763/2097152000000), 0]

theorem checked0433 :
    (∀ i, 0 ≤ plusWeights0433 i) ∧
    (∀ i, 0 ≤ minusWeights0433 i) ∧
    (∀ i, plusCoefficients coefficients0433 upper0433 i = powerCoefficients10 plusWeights0433 i) ∧
    (∀ i, minusCoefficients coefficients0433 upper0433 i = powerCoefficients10 minusWeights0433 i) := by
  decide +kernel

theorem bound0433 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0433 g| ≤ (upper0433 : ℝ) :=
  abs_of_coefficients coefficients0433 upper0433 powerCoefficients10 plusWeights0433 minusWeights0433
    checked0433.1 checked0433.2.1 checked0433.2.2.1 checked0433.2.2.2
    (power_identity10 plusWeights0433) (power_identity10 minusWeights0433) g hg hmax

def envelope0433 : Envelope := ⟨coefficients0433, upper0433, bound0433⟩

def coefficients0434 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (9/512), (13/4096), (1547/32768), (1439/65536), (7775/524288)]

def upper0434 : ℚ := (19284419/1048576000000000)

def plusWeights0434 : Fin 11 → ℚ := ![(19284419/1048576000000000), (19284419/104857600000000), (173559771/209715200000000), (57853257/26214400000000), (404972799/104857600000000), (1214918397/262144000000000), (406815999/104857600000000), (59704777/26214400000000), (195976859/209715200000000), (134291847/524288000000000), (19284419/524288000000000)]

def minusWeights0434 : Fin 11 → ℚ := ![(19284419/1048576000000000), (19284419/104857600000000), (173559771/209715200000000), (57853257/26214400000000), (404972799/104857600000000), (1214918397/262144000000000), (403129599/104857600000000), (56001737/26214400000000), (151142683/209715200000000), (58552343/524288000000000), 0]

theorem checked0434 :
    (∀ i, 0 ≤ plusWeights0434 i) ∧
    (∀ i, 0 ≤ minusWeights0434 i) ∧
    (∀ i, plusCoefficients coefficients0434 upper0434 i = powerCoefficients10 plusWeights0434 i) ∧
    (∀ i, minusCoefficients coefficients0434 upper0434 i = powerCoefficients10 minusWeights0434 i) := by
  decide +kernel

theorem bound0434 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0434 g| ≤ (upper0434 : ℝ) :=
  abs_of_coefficients coefficients0434 upper0434 powerCoefficients10 plusWeights0434 minusWeights0434
    checked0434.1 checked0434.2.1 checked0434.2.2.1 checked0434.2.2.2
    (power_identity10 plusWeights0434) (power_identity10 minusWeights0434) g hg hmax

def envelope0434 : Envelope := ⟨coefficients0434, upper0434, bound0434⟩

def coefficients0435 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (21/1024), (357/8192), (39/2048), (63/4096), (15/4096)]

def upper0435 : ℚ := (205389/8192000000000)

def plusWeights0435 : Fin 11 → ℚ := ![(205389/8192000000000), (205389/819200000000), (1848501/1638400000000), (616167/204800000000), (4313169/819200000000), (12939507/2048000000000), (4329969/819200000000), (1267719/409600000000), (2071833/1638400000000), (709059/2048000000000), (205389/4096000000000)]

def minusWeights0435 : Fin 11 → ℚ := ![(205389/8192000000000), (205389/819200000000), (1848501/1638400000000), (616167/204800000000), (4313169/819200000000), (12939507/2048000000000), (4296369/819200000000), (1196949/409600000000), (1625169/1638400000000), (158943/1024000000000), 0]

theorem checked0435 :
    (∀ i, 0 ≤ plusWeights0435 i) ∧
    (∀ i, 0 ≤ minusWeights0435 i) ∧
    (∀ i, plusCoefficients coefficients0435 upper0435 i = powerCoefficients10 plusWeights0435 i) ∧
    (∀ i, minusCoefficients coefficients0435 upper0435 i = powerCoefficients10 minusWeights0435 i) := by
  decide +kernel

theorem bound0435 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0435 g| ≤ (upper0435 : ℝ) :=
  abs_of_coefficients coefficients0435 upper0435 powerCoefficients10 plusWeights0435 minusWeights0435
    checked0435.1 checked0435.2.1 checked0435.2.2.1 checked0435.2.2.2
    (power_identity10 plusWeights0435) (power_identity10 minusWeights0435) g hg hmax

def envelope0435 : Envelope := ⟨coefficients0435, upper0435, bound0435⟩

def coefficients0436 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (45/2048), (15/1024), (945/32768), (1245/65536), (2595/262144)]

def upper0436 : ℚ := (12449679/524288000000000)

def plusWeights0436 : Fin 11 → ℚ := ![(12449679/524288000000000), (12449679/52428800000000), (112047111/104857600000000), (37349037/13107200000000), (261443259/52428800000000), (784329777/131072000000000), (262595259/52428800000000), (38520237/13107200000000), (126362151/104857600000000), (3463863/10485760000000), (12449679/262144000000000)]

def minusWeights0436 : Fin 11 → ℚ := ![(12449679/524288000000000), (12449679/52428800000000), (112047111/104857600000000), (37349037/13107200000000), (261443259/52428800000000), (784329777/131072000000000), (260291259/52428800000000), (36177837/13107200000000), (97732071/104857600000000), (7580043/52428800000000), 0]

theorem checked0436 :
    (∀ i, 0 ≤ plusWeights0436 i) ∧
    (∀ i, 0 ≤ minusWeights0436 i) ∧
    (∀ i, plusCoefficients coefficients0436 upper0436 i = powerCoefficients10 plusWeights0436 i) ∧
    (∀ i, minusCoefficients coefficients0436 upper0436 i = powerCoefficients10 minusWeights0436 i) := by
  decide +kernel

theorem bound0436 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0436 g| ≤ (upper0436 : ℝ) :=
  abs_of_coefficients coefficients0436 upper0436 powerCoefficients10 plusWeights0436 minusWeights0436
    checked0436.1 checked0436.2.1 checked0436.2.2.1 checked0436.2.2.2
    (power_identity10 plusWeights0436) (power_identity10 minusWeights0436) g hg hmax

def envelope0436 : Envelope := ⟨coefficients0436, upper0436, bound0436⟩

def coefficients0437 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/1024), (-93/4096), (1749/16384), (1713/32768), (6615/131072)]

def upper0437 : ℚ := (6611667/262144000000000)

def plusWeights0437 : Fin 11 → ℚ := ![(6611667/262144000000000), (6611667/26214400000000), (59505003/52428800000000), (19835001/6553600000000), (138845007/26214400000000), (416535021/65536000000000), (139536207/26214400000000), (20511321/6553600000000), (67498251/52428800000000), (46276227/131072000000000), (6611667/131072000000000)]

def minusWeights0437 : Fin 11 → ℚ := ![(6611667/262144000000000), (6611667/26214400000000), (59505003/52428800000000), (19835001/6553600000000), (138845007/26214400000000), (416535021/65536000000000), (138153807/26214400000000), (19158681/6553600000000), (10302351/10485760000000), (19840443/131072000000000), 0]

theorem checked0437 :
    (∀ i, 0 ≤ plusWeights0437 i) ∧
    (∀ i, 0 ≤ minusWeights0437 i) ∧
    (∀ i, plusCoefficients coefficients0437 upper0437 i = powerCoefficients10 plusWeights0437 i) ∧
    (∀ i, minusCoefficients coefficients0437 upper0437 i = powerCoefficients10 minusWeights0437 i) := by
  decide +kernel

theorem bound0437 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0437 g| ≤ (upper0437 : ℝ) :=
  abs_of_coefficients coefficients0437 upper0437 powerCoefficients10 plusWeights0437 minusWeights0437
    checked0437.1 checked0437.2.1 checked0437.2.2.1 checked0437.2.2.2
    (power_identity10 plusWeights0437) (power_identity10 minusWeights0437) g hg hmax

def envelope0437 : Envelope := ⟨coefficients0437, upper0437, bound0437⟩

def coefficients0438 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/1024), (-93/4096), (57/512), (261/4096), (25305/262144)]

def upper0438 : ℚ := (13255749/524288000000000)

def plusWeights0438 : Fin 11 → ℚ := ![(13255749/524288000000000), (13255749/52428800000000), (119301741/104857600000000), (39767247/13107200000000), (278370729/52428800000000), (835112187/131072000000000), (279753129/52428800000000), (41119887/13107200000000), (135293037/104857600000000), (92741529/262144000000000), (13255749/262144000000000)]

def minusWeights0438 : Fin 11 → ℚ := ![(13255749/524288000000000), (13255749/52428800000000), (119301741/104857600000000), (39767247/13107200000000), (278370729/52428800000000), (835112187/131072000000000), (276988329/52428800000000), (38414607/13107200000000), (20662089/20971520000000), (39815961/262144000000000), 0]

theorem checked0438 :
    (∀ i, 0 ≤ plusWeights0438 i) ∧
    (∀ i, 0 ≤ minusWeights0438 i) ∧
    (∀ i, plusCoefficients coefficients0438 upper0438 i = powerCoefficients10 plusWeights0438 i) ∧
    (∀ i, minusCoefficients coefficients0438 upper0438 i = powerCoefficients10 minusWeights0438 i) := by
  decide +kernel

theorem bound0438 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0438 g| ≤ (upper0438 : ℝ) :=
  abs_of_coefficients coefficients0438 upper0438 powerCoefficients10 plusWeights0438 minusWeights0438
    checked0438.1 checked0438.2.1 checked0438.2.2.1 checked0438.2.2.2
    (power_identity10 plusWeights0438) (power_identity10 minusWeights0438) g hg hmax

def envelope0438 : Envelope := ⟨coefficients0438, upper0438, bound0438⟩

def coefficients0439 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/1024), (-93/4096), (1869/16384), (1953/32768), (1185/16384)]

def upper0439 : ℚ := (82917/3276800000000)

def plusWeights0439 : Fin 11 → ℚ := ![(82917/3276800000000), (82917/327680000000), (746253/655360000000), (248751/81920000000), (1741257/327680000000), (5223771/819200000000), (1749897/327680000000), (51441/16384000000), (4231083/3276800000000), (11601213/32768000000000), (82917/1638400000000)]

def minusWeights0439 : Fin 11 → ℚ := ![(82917/3276800000000), (82917/327680000000), (746253/655360000000), (248751/81920000000), (1741257/327680000000), (5223771/819200000000), (1732617/327680000000), (240297/81920000000), (3231447/3276800000000), (4982187/32768000000000), 0]

theorem checked0439 :
    (∀ i, 0 ≤ plusWeights0439 i) ∧
    (∀ i, 0 ≤ minusWeights0439 i) ∧
    (∀ i, plusCoefficients coefficients0439 upper0439 i = powerCoefficients10 plusWeights0439 i) ∧
    (∀ i, minusCoefficients coefficients0439 upper0439 i = powerCoefficients10 minusWeights0439 i) := by
  decide +kernel

theorem bound0439 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0439 g| ≤ (upper0439 : ℝ) :=
  abs_of_coefficients coefficients0439 upper0439 powerCoefficients10 plusWeights0439 minusWeights0439
    checked0439.1 checked0439.2.1 checked0439.2.2.1 checked0439.2.2.2
    (power_identity10 plusWeights0439) (power_identity10 minusWeights0439) g hg hmax

def envelope0439 : Envelope := ⟨coefficients0439, upper0439, bound0439⟩

def coefficients0440 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/1024), (39/8192), (3273/32768), (3801/65536), (44235/524288)]

def upper0440 : ℚ := (29264223/1048576000000000)

def plusWeights0440 : Fin 11 → ℚ := ![(29264223/1048576000000000), (29264223/104857600000000), (263378007/209715200000000), (87792669/26214400000000), (614548683/104857600000000), (1843646049/262144000000000), (617313483/104857600000000), (90569949/26214400000000), (297064599/209715200000000), (203443683/524288000000000), (29264223/524288000000000)]

def minusWeights0440 : Fin 11 → ℚ := ![(29264223/1048576000000000), (29264223/104857600000000), (263378007/209715200000000), (87792669/26214400000000), (614548683/104857600000000), (1843646049/262144000000000), (611783883/104857600000000), (85015389/26214400000000), (45938283/41943040000000), (89198547/524288000000000), 0]

theorem checked0440 :
    (∀ i, 0 ≤ plusWeights0440 i) ∧
    (∀ i, 0 ≤ minusWeights0440 i) ∧
    (∀ i, plusCoefficients coefficients0440 upper0440 i = powerCoefficients10 plusWeights0440 i) ∧
    (∀ i, minusCoefficients coefficients0440 upper0440 i = powerCoefficients10 minusWeights0440 i) := by
  decide +kernel

theorem bound0440 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0440 g| ≤ (upper0440 : ℝ) :=
  abs_of_coefficients coefficients0440 upper0440 powerCoefficients10 plusWeights0440 minusWeights0440
    checked0440.1 checked0440.2.1 checked0440.2.2.1 checked0440.2.2.2
    (power_identity10 plusWeights0440) (power_identity10 minusWeights0440) g hg hmax

def envelope0440 : Envelope := ⟨coefficients0440, upper0440, bound0440⟩

def coefficients0441 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (27/1024), (57/4096), (1149/16384), (1113/32768), (33855/262144)]

def upper0441 : ℚ := (14945859/524288000000000)

def plusWeights0441 : Fin 11 → ℚ := ![(14945859/524288000000000), (14945859/52428800000000), (134512731/104857600000000), (44837577/13107200000000), (313863039/52428800000000), (941589117/131072000000000), (315245439/52428800000000), (46238217/13107200000000), (151612827/104857600000000), (103848279/262144000000000), (14945859/262144000000000)]

def minusWeights0441 : Fin 11 → ℚ := ![(14945859/524288000000000), (14945859/52428800000000), (134512731/104857600000000), (44837577/13107200000000), (313863039/52428800000000), (941589117/131072000000000), (312480639/52428800000000), (43436937/13107200000000), (23482527/20971520000000), (45610311/262144000000000), 0]

theorem checked0441 :
    (∀ i, 0 ≤ plusWeights0441 i) ∧
    (∀ i, 0 ≤ minusWeights0441 i) ∧
    (∀ i, plusCoefficients coefficients0441 upper0441 i = powerCoefficients10 plusWeights0441 i) ∧
    (∀ i, minusCoefficients coefficients0441 upper0441 i = powerCoefficients10 minusWeights0441 i) := by
  decide +kernel

theorem bound0441 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0441 g| ≤ (upper0441 : ℝ) :=
  abs_of_coefficients coefficients0441 upper0441 powerCoefficients10 plusWeights0441 minusWeights0441
    checked0441.1 checked0441.2.1 checked0441.2.2.1 checked0441.2.2.2
    (power_identity10 plusWeights0441) (power_identity10 minusWeights0441) g hg hmax

def envelope0441 : Envelope := ⟨coefficients0441, upper0441, bound0441⟩

def coefficients0442 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (7/256), (163/4096), (89/4096), (69/4096), (65/16384)]

def upper0442 : ℚ := (206817/6553600000000)

def plusWeights0442 : Fin 11 → ℚ := ![(206817/6553600000000), (206817/655360000000), (1861353/1310720000000), (620451/163840000000), (4343157/655360000000), (13029471/1638400000000), (4361077/655360000000), (639023/163840000000), (10461629/6553600000000), (7165421/16384000000000), (206817/3276800000000)]

def minusWeights0442 : Fin 11 → ℚ := ![(206817/6553600000000), (206817/655360000000), (1861353/1310720000000), (620451/163840000000), (4343157/655360000000), (13029471/1638400000000), (4325237/655360000000), (601879/163840000000), (8151901/6553600000000), (3175429/16384000000000), 0]

theorem checked0442 :
    (∀ i, 0 ≤ plusWeights0442 i) ∧
    (∀ i, 0 ≤ minusWeights0442 i) ∧
    (∀ i, plusCoefficients coefficients0442 upper0442 i = powerCoefficients10 plusWeights0442 i) ∧
    (∀ i, minusCoefficients coefficients0442 upper0442 i = powerCoefficients10 minusWeights0442 i) := by
  decide +kernel

theorem bound0442 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0442 g| ≤ (upper0442 : ℝ) :=
  abs_of_coefficients coefficients0442 upper0442 powerCoefficients10 plusWeights0442 minusWeights0442
    checked0442.1 checked0442.2.1 checked0442.2.2.1 checked0442.2.2.2
    (power_identity10 plusWeights0442) (power_identity10 minusWeights0442) g hg hmax

def envelope0442 : Envelope := ⟨coefficients0442, upper0442, bound0442⟩

def coefficients0443 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/512), (-213/2048), (-267/2048), (-2703/16384), (-2121/32768)]

def upper0443 : ℚ := (5708619/327680000000000)

def plusWeights0443 : Fin 11 → ℚ := ![(5708619/327680000000000), (5708619/32768000000000), (51377571/65536000000000), (17125857/8192000000000), (119880999/32768000000000), (359642997/81920000000000), (120840999/32768000000000), (18000657/8192000000000), (60767331/65536000000000), (8435373/32768000000000), (5708619/163840000000000)]

def minusWeights0443 : Fin 11 → ℚ := ![(5708619/327680000000000), (5708619/32768000000000), (51377571/65536000000000), (17125857/8192000000000), (119880999/32768000000000), (359642997/81920000000000), (118920999/32768000000000), (16251057/8192000000000), (41987811/65536000000000), (596373/6553600000000), 0]

theorem checked0443 :
    (∀ i, 0 ≤ plusWeights0443 i) ∧
    (∀ i, 0 ≤ minusWeights0443 i) ∧
    (∀ i, plusCoefficients coefficients0443 upper0443 i = powerCoefficients10 plusWeights0443 i) ∧
    (∀ i, minusCoefficients coefficients0443 upper0443 i = powerCoefficients10 minusWeights0443 i) := by
  decide +kernel

theorem bound0443 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0443 g| ≤ (upper0443 : ℝ) :=
  abs_of_coefficients coefficients0443 upper0443 powerCoefficients10 plusWeights0443 minusWeights0443
    checked0443.1 checked0443.2.1 checked0443.2.2.1 checked0443.2.2.2
    (power_identity10 plusWeights0443) (power_identity10 minusWeights0443) g hg hmax

def envelope0443 : Envelope := ⟨coefficients0443, upper0443, bound0443⟩

def coefficients0444 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/512), (-105/2048), (-135/2048), (-945/16384), (-675/32768)]

def upper0444 : ℚ := (307377/13107200000000)

def plusWeights0444 : Fin 11 → ℚ := ![(307377/13107200000000), (307377/1310720000000), (2766393/2621440000000), (922131/327680000000), (6454917/1310720000000), (19364751/3276800000000), (6493317/1310720000000), (958851/327680000000), (637029/524288000000), (2195067/6553600000000), (307377/6553600000000)]

def minusWeights0444 : Fin 11 → ℚ := ![(307377/13107200000000), (307377/1310720000000), (2766393/2621440000000), (922131/327680000000), (6454917/1310720000000), (19364751/3276800000000), (6416517/1310720000000), (885411/327680000000), (2347641/2621440000000), (878703/6553600000000), 0]

theorem checked0444 :
    (∀ i, 0 ≤ plusWeights0444 i) ∧
    (∀ i, 0 ≤ minusWeights0444 i) ∧
    (∀ i, plusCoefficients coefficients0444 upper0444 i = powerCoefficients10 plusWeights0444 i) ∧
    (∀ i, minusCoefficients coefficients0444 upper0444 i = powerCoefficients10 minusWeights0444 i) := by
  decide +kernel

theorem bound0444 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0444 g| ≤ (upper0444 : ℝ) :=
  abs_of_coefficients coefficients0444 upper0444 powerCoefficients10 plusWeights0444 minusWeights0444
    checked0444.1 checked0444.2.1 checked0444.2.2.1 checked0444.2.2.2
    (power_identity10 plusWeights0444) (power_identity10 minusWeights0444) g hg hmax

def envelope0444 : Envelope := ⟨coefficients0444, upper0444, bound0444⟩

def coefficients0445 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/512), (-65/2048), (-95/2048), (-855/32768), (-475/65536)]

def upper0445 : ℚ := (671937/26214400000000)

def plusWeights0445 : Fin 11 → ℚ := ![(671937/26214400000000), (671937/2621440000000), (6047433/5242880000000), (2015811/655360000000), (14110677/2621440000000), (42332031/6553600000000), (14187477/2621440000000), (2090531/655360000000), (6916681/5242880000000), (4758383/13107200000000), (671937/13107200000000)]

def minusWeights0445 : Fin 11 → ℚ := ![(671937/26214400000000), (671937/2621440000000), (6047433/5242880000000), (2015811/655360000000), (14110677/2621440000000), (42332031/6553600000000), (14033877/2621440000000), (1941091/655360000000), (1035637/1048576000000), (1960987/13107200000000), 0]

theorem checked0445 :
    (∀ i, 0 ≤ plusWeights0445 i) ∧
    (∀ i, 0 ≤ minusWeights0445 i) ∧
    (∀ i, plusCoefficients coefficients0445 upper0445 i = powerCoefficients10 plusWeights0445 i) ∧
    (∀ i, minusCoefficients coefficients0445 upper0445 i = powerCoefficients10 minusWeights0445 i) := by
  decide +kernel

theorem bound0445 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0445 g| ≤ (upper0445 : ℝ) :=
  abs_of_coefficients coefficients0445 upper0445 powerCoefficients10 plusWeights0445 minusWeights0445
    checked0445.1 checked0445.2.1 checked0445.2.2.1 checked0445.2.2.2
    (power_identity10 plusWeights0445) (power_identity10 minusWeights0445) g hg hmax

def envelope0445 : Envelope := ⟨coefficients0445, upper0445, bound0445⟩

def coefficients0446 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/512), (-5/512), (-25/1024), (-225/16384), (-125/32768)]

def upper0446 : ℚ := (73563/2621440000000)

def plusWeights0446 : Fin 11 → ℚ := ![(73563/2621440000000), (73563/262144000000), (662067/524288000000), (220689/65536000000), (1544823/262144000000), (4634469/655360000000), (1552503/262144000000), (45661/13107200000), (752563/524288000000), (516917/1310720000000), (73563/1310720000000)]

def minusWeights0446 : Fin 11 → ℚ := ![(73563/2621440000000), (73563/262144000000), (662067/524288000000), (220689/65536000000), (1544823/262144000000), (4634469/655360000000), (1537143/262144000000), (213073/65536000000), (571571/524288000000), (218713/1310720000000), 0]

theorem checked0446 :
    (∀ i, 0 ≤ plusWeights0446 i) ∧
    (∀ i, 0 ≤ minusWeights0446 i) ∧
    (∀ i, plusCoefficients coefficients0446 upper0446 i = powerCoefficients10 plusWeights0446 i) ∧
    (∀ i, minusCoefficients coefficients0446 upper0446 i = powerCoefficients10 minusWeights0446 i) := by
  decide +kernel

theorem bound0446 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0446 g| ≤ (upper0446 : ℝ) :=
  abs_of_coefficients coefficients0446 upper0446 powerCoefficients10 plusWeights0446 minusWeights0446
    checked0446.1 checked0446.2.1 checked0446.2.2.1 checked0446.2.2.2
    (power_identity10 plusWeights0446) (power_identity10 minusWeights0446) g hg hmax

def envelope0446 : Envelope := ⟨coefficients0446, upper0446, bound0446⟩

def coefficients0447 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, (15/512), (-15/2048), (-45/2048), (-405/32768), (-225/65536)]

def upper0447 : ℚ := (742707/26214400000000)

def plusWeights0447 : Fin 11 → ℚ := ![(742707/26214400000000), (742707/2621440000000), (6684363/5242880000000), (2228121/655360000000), (15596847/2621440000000), (46790541/6553600000000), (15673647/2621440000000), (2304441/655360000000), (7593291/5242880000000), (5214813/13107200000000), (742707/13107200000000)]

def minusWeights0447 : Fin 11 → ℚ := ![(742707/26214400000000), (742707/2621440000000), (6684363/5242880000000), (2228121/655360000000), (15596847/2621440000000), (46790541/6553600000000), (15520047/2621440000000), (2151801/655360000000), (1155087/1048576000000), (2212257/13107200000000), 0]

theorem checked0447 :
    (∀ i, 0 ≤ plusWeights0447 i) ∧
    (∀ i, 0 ≤ minusWeights0447 i) ∧
    (∀ i, plusCoefficients coefficients0447 upper0447 i = powerCoefficients10 plusWeights0447 i) ∧
    (∀ i, minusCoefficients coefficients0447 upper0447 i = powerCoefficients10 minusWeights0447 i) := by
  decide +kernel

theorem bound0447 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0447 g| ≤ (upper0447 : ℝ) :=
  abs_of_coefficients coefficients0447 upper0447 powerCoefficients10 plusWeights0447 minusWeights0447
    checked0447.1 checked0447.2.1 checked0447.2.2.1 checked0447.2.2.2
    (power_identity10 plusWeights0447) (power_identity10 minusWeights0447) g hg hmax

def envelope0447 : Envelope := ⟨coefficients0447, upper0447, bound0447⟩

end BilayerDressed.CubicQuarticEnvelopes

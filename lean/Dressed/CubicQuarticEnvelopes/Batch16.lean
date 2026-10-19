import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0512 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (1/16), (53/128), (1/4), (945/4096), (1425/8192), (2775/65536)]

def upper0512 : ℚ := (27958911/26214400000000)

def plusWeights0512 : Fin 11 → ℚ := ![(27958911/26214400000000), (27958911/2621440000000), (251630199/5242880000000), (83876733/655360000000), (587137131/2621440000000), (1765507393/6553600000000), (596414571/2621440000000), (89074557/655360000000), (297828791/5242880000000), (40701831/2621440000000), (27958911/13107200000000)]

def minusWeights0512 : Fin 11 → ℚ := ![(27958911/26214400000000), (27958911/2621440000000), (251630199/5242880000000), (83876733/655360000000), (587137131/2621440000000), (1757315393/6553600000000), (577859691/2621440000000), (78678909/655360000000), (205431607/5242880000000), (15215991/2621440000000), 0]

theorem checked0512 :
    (∀ i, 0 ≤ plusWeights0512 i) ∧
    (∀ i, 0 ≤ minusWeights0512 i) ∧
    (∀ i, plusCoefficients coefficients0512 upper0512 i = powerCoefficients10 plusWeights0512 i) ∧
    (∀ i, minusCoefficients coefficients0512 upper0512 i = powerCoefficients10 minusWeights0512 i) := by
  decide +kernel

theorem bound0512 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0512 g| ≤ (upper0512 : ℝ) :=
  abs_of_coefficients coefficients0512 upper0512 powerCoefficients10 plusWeights0512 minusWeights0512
    checked0512.1 checked0512.2.1 checked0512.2.2.1 checked0512.2.2.2
    (power_identity10 plusWeights0512) (power_identity10 minusWeights0512) g hg hmax

def envelope0512 : Envelope := ⟨coefficients0512, upper0512, bound0512⟩

def coefficients0513 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (45/512), (171/1024), (1167/8192), (51/512), (159/2048), (75/4096)]

def upper0513 : ℚ := (8693511/8192000000000)

def plusWeights0513 : Fin 11 → ℚ := ![(8693511/8192000000000), (8693511/819200000000), (78241599/1638400000000), (26080533/204800000000), (182563731/819200000000), (549491193/2048000000000), (186300531/819200000000), (56040501/409600000000), (94354851/1638400000000), (64387083/4096000000000), (8693511/4096000000000)]

def minusWeights0513 : Fin 11 → ℚ := ![(8693511/8192000000000), (8693511/819200000000), (78241599/1638400000000), (26080533/204800000000), (182563731/819200000000), (545891193/2048000000000), (178826931/819200000000), (48281631/409600000000), (62128347/1638400000000), (22548027/4096000000000), 0]

theorem checked0513 :
    (∀ i, 0 ≤ plusWeights0513 i) ∧
    (∀ i, 0 ≤ minusWeights0513 i) ∧
    (∀ i, plusCoefficients coefficients0513 upper0513 i = powerCoefficients10 plusWeights0513 i) ∧
    (∀ i, minusCoefficients coefficients0513 upper0513 i = powerCoefficients10 minusWeights0513 i) := by
  decide +kernel

theorem bound0513 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0513 g| ≤ (upper0513 : ℝ) :=
  abs_of_coefficients coefficients0513 upper0513 powerCoefficients10 plusWeights0513 minusWeights0513
    checked0513.1 checked0513.2.1 checked0513.2.2.1 checked0513.2.2.2
    (power_identity10 plusWeights0513) (power_identity10 minusWeights0513) g hg hmax

def envelope0513 : Envelope := ⟨coefficients0513, upper0513, bound0513⟩

def coefficients0514 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/128), (-1/32), (29/2048), (145/4096), (1605/32768), (1385/65536), (3925/524288)]

def upper0514 : ℚ := (102123309/209715200000000)

def plusWeights0514 : Fin 11 → ℚ := ![(102123309/209715200000000), (102123309/20971520000000), (919109781/41943040000000), (306369927/5242880000000), (2160973489/20971520000000), (6663144467/52428800000000), (2357878449/20971520000000), (372221447/5242880000000), (256717457/8388608000000), (845454281/104857600000000), (102123309/104857600000000)]

def minusWeights0514 : Fin 11 → ℚ := ![(102123309/209715200000000), (102123309/20971520000000), (919109781/41943040000000), (306369927/5242880000000), (2128205489/20971520000000), (6204392467/52428800000000), (1931300529/20971520000000), (240518407/5242880000000), (554632277/41943040000000), (175778809/104857600000000), 0]

theorem checked0514 :
    (∀ i, 0 ≤ plusWeights0514 i) ∧
    (∀ i, 0 ≤ minusWeights0514 i) ∧
    (∀ i, plusCoefficients coefficients0514 upper0514 i = powerCoefficients10 plusWeights0514 i) ∧
    (∀ i, minusCoefficients coefficients0514 upper0514 i = powerCoefficients10 minusWeights0514 i) := by
  decide +kernel

theorem bound0514 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0514 g| ≤ (upper0514 : ℝ) :=
  abs_of_coefficients coefficients0514 upper0514 powerCoefficients10 plusWeights0514 minusWeights0514
    checked0514.1 checked0514.2.1 checked0514.2.2.1 checked0514.2.2.2
    (power_identity10 plusWeights0514) (power_identity10 minusWeights0514) g hg hmax

def envelope0514 : Envelope := ⟨coefficients0514, upper0514, bound0514⟩

def coefficients0515 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/64), (-23/512), (-19/512), (-119/1024), (-431/4096), (-2799/32768), (-1833/65536)]

def upper0515 : ℚ := (696916587/655360000000000)

def plusWeights0515 : Fin 11 → ℚ := ![(696916587/655360000000000), (696916587/65536000000000), (6272249283/131072000000000), (2090749761/16384000000000), (14737648327/65536000000000), (45368144981/163840000000000), (16021616327/65536000000000), (2526527361/16384000000000), (8721557763/131072000000000), (1151960269/65536000000000), (696916587/327680000000000)]

def minusWeights0515 : Fin 11 → ℚ := ![(696916587/655360000000000), (696916587/65536000000000), (6272249283/131072000000000), (2090749761/16384000000000), (14532848327/65536000000000), (42443344981/163840000000000), (13248880327/65536000000000), (1654972161/16384000000000), (3822940803/131072000000000), (48374581/13107200000000), 0]

theorem checked0515 :
    (∀ i, 0 ≤ plusWeights0515 i) ∧
    (∀ i, 0 ≤ minusWeights0515 i) ∧
    (∀ i, plusCoefficients coefficients0515 upper0515 i = powerCoefficients10 plusWeights0515 i) ∧
    (∀ i, minusCoefficients coefficients0515 upper0515 i = powerCoefficients10 minusWeights0515 i) := by
  decide +kernel

theorem bound0515 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0515 g| ≤ (upper0515 : ℝ) :=
  abs_of_coefficients coefficients0515 upper0515 powerCoefficients10 plusWeights0515 minusWeights0515
    checked0515.1 checked0515.2.1 checked0515.2.2.1 checked0515.2.2.2
    (power_identity10 plusWeights0515) (power_identity10 minusWeights0515) g hg hmax

def envelope0515 : Envelope := ⟨coefficients0515, upper0515, bound0515⟩

def coefficients0516 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/64), (-19/512), (-21/512), (-49/512), (-267/4096), (-1485/32768), (-975/65536)]

def upper0516 : ℚ := (5977521/5242880000000)

def plusWeights0516 : Fin 11 → ℚ := ![(5977521/5242880000000), (5977521/524288000000), (53797689/1048576000000), (17932563/131072000000), (126347141/524288000000), (388385423/1310720000000), (136821637/524288000000), (107597023/655360000000), (1854841297/26214400000000), (245453623/13107200000000), (5977521/2621440000000)]

def minusWeights0516 : Fin 11 → ℚ := ![(5977521/5242880000000), (5977521/524288000000), (53797689/1048576000000), (17932563/131072000000), (124708741/524288000000), (364782223/1310720000000), (22846849/104857600000), (71728607/655360000000), (835043153/26214400000000), (53422427/13107200000000), 0]

theorem checked0516 :
    (∀ i, 0 ≤ plusWeights0516 i) ∧
    (∀ i, 0 ≤ minusWeights0516 i) ∧
    (∀ i, plusCoefficients coefficients0516 upper0516 i = powerCoefficients10 plusWeights0516 i) ∧
    (∀ i, minusCoefficients coefficients0516 upper0516 i = powerCoefficients10 minusWeights0516 i) := by
  decide +kernel

theorem bound0516 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0516 g| ≤ (upper0516 : ℝ) :=
  abs_of_coefficients coefficients0516 upper0516 powerCoefficients10 plusWeights0516 minusWeights0516
    checked0516.1 checked0516.2.1 checked0516.2.2.1 checked0516.2.2.2
    (power_identity10 plusWeights0516) (power_identity10 minusWeights0516) g hg hmax

def envelope0516 : Envelope := ⟨coefficients0516, upper0516, bound0516⟩

def coefficients0517 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/64), (-19/512), (-37/1024), (-427/4096), (-39/512), (-225/4096), (-75/4096)]

def upper0517 : ℚ := (1874379/1638400000000)

def plusWeights0517 : Fin 11 → ℚ := ![(1874379/1638400000000), (1874379/163840000000), (16869411/327680000000), (5623137/40960000000), (39617959/163840000000), (121773877/409600000000), (42892039/163840000000), (674479/4096000000), (116259367/1638400000000), (7693291/409600000000), (1874379/819200000000)]

def minusWeights0517 : Fin 11 → ℚ := ![(1874379/1638400000000), (1874379/163840000000), (16869411/327680000000), (5623137/40960000000), (39105959/163840000000), (114397877/409600000000), (35831879/163840000000), (1125371/10240000000), (52434743/1638400000000), (419651/102400000000), 0]

theorem checked0517 :
    (∀ i, 0 ≤ plusWeights0517 i) ∧
    (∀ i, 0 ≤ minusWeights0517 i) ∧
    (∀ i, plusCoefficients coefficients0517 upper0517 i = powerCoefficients10 plusWeights0517 i) ∧
    (∀ i, minusCoefficients coefficients0517 upper0517 i = powerCoefficients10 minusWeights0517 i) := by
  decide +kernel

theorem bound0517 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0517 g| ≤ (upper0517 : ℝ) :=
  abs_of_coefficients coefficients0517 upper0517 powerCoefficients10 plusWeights0517 minusWeights0517
    checked0517.1 checked0517.2.1 checked0517.2.2.1 checked0517.2.2.2
    (power_identity10 plusWeights0517) (power_identity10 minusWeights0517) g hg hmax

def envelope0517 : Envelope := ⟨coefficients0517, upper0517, bound0517⟩

def coefficients0518 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/64), (-5/512), (-15/1024), (-441/8192), (-47/1024), (-95/4096), (-25/4096)]

def upper0518 : ℚ := (2366389/1638400000000)

def plusWeights0518 : Fin 11 → ℚ := ![(2366389/1638400000000), (2366389/163840000000), (21297501/327680000000), (7099167/40960000000), (49950169/163840000000), (152882507/409600000000), (53451769/163840000000), (16673093/81920000000), (143116293/1638400000000), (2381243/102400000000), (2366389/819200000000)]

def minusWeights0518 : Fin 11 → ℚ := ![(2366389/1638400000000), (2366389/163840000000), (21297501/327680000000), (7099167/40960000000), (49438169/163840000000), (145282507/409600000000), (45936569/163840000000), (468943/3276800000), (69858717/1638400000000), (2306973/409600000000), 0]

theorem checked0518 :
    (∀ i, 0 ≤ plusWeights0518 i) ∧
    (∀ i, 0 ≤ minusWeights0518 i) ∧
    (∀ i, plusCoefficients coefficients0518 upper0518 i = powerCoefficients10 plusWeights0518 i) ∧
    (∀ i, minusCoefficients coefficients0518 upper0518 i = powerCoefficients10 minusWeights0518 i) := by
  decide +kernel

theorem bound0518 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0518 g| ≤ (upper0518 : ℝ) :=
  abs_of_coefficients coefficients0518 upper0518 powerCoefficients10 plusWeights0518 minusWeights0518
    checked0518.1 checked0518.2.1 checked0518.2.2.1 checked0518.2.2.2
    (power_identity10 plusWeights0518) (power_identity10 minusWeights0518) g hg hmax

def envelope0518 : Envelope := ⟨coefficients0518, upper0518, bound0518⟩

def coefficients0519 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/64), (-1/512), (-1/128), (-273/8192), (-57/2048), (-235/16384), (-125/32768)]

def upper0519 : ℚ := (20074079/13107200000000)

def plusWeights0519 : Fin 11 → ℚ := ![(20074079/13107200000000), (20074079/1310720000000), (180666711/2621440000000), (60222237/327680000000), (423603659/1310720000000), (1295322977/3276800000000), (452137419/1310720000000), (14077381/65536000000), (1207224467/13107200000000), (160896333/6553600000000), (20074079/6553600000000)]

def minusWeights0519 : Fin 11 → ℚ := ![(20074079/13107200000000), (20074079/1310720000000), (180666711/2621440000000), (60222237/327680000000), (419507659/1310720000000), (1234010977/3276800000000), (390973899/1310720000000), (50057569/327680000000), (599442643/13107200000000), (39844457/6553600000000), 0]

theorem checked0519 :
    (∀ i, 0 ≤ plusWeights0519 i) ∧
    (∀ i, 0 ≤ minusWeights0519 i) ∧
    (∀ i, plusCoefficients coefficients0519 upper0519 i = powerCoefficients10 plusWeights0519 i) ∧
    (∀ i, minusCoefficients coefficients0519 upper0519 i = powerCoefficients10 minusWeights0519 i) := by
  decide +kernel

theorem bound0519 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0519 g| ≤ (upper0519 : ℝ) :=
  abs_of_coefficients coefficients0519 upper0519 powerCoefficients10 plusWeights0519 minusWeights0519
    checked0519.1 checked0519.2.1 checked0519.2.2.1 checked0519.2.2.2
    (power_identity10 plusWeights0519) (power_identity10 minusWeights0519) g hg hmax

def envelope0519 : Envelope := ⟨coefficients0519, upper0519, bound0519⟩

def coefficients0520 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/128), (-1/512), (121/2048), (449/8192), (2947/32768), (3059/65536), (3995/131072)]

def upper0520 : ℚ := (125290719/52428800000000)

def plusWeights0520 : Fin 11 → ℚ := ![(125290719/52428800000000), (125290719/5242880000000), (1127616471/10485760000000), (375872157/1310720000000), (2643393099/5242880000000), (8077379297/13107200000000), (2815222859/5242880000000), (437373101/1310720000000), (7490537187/52428800000000), (4996041053/131072000000000), (125290719/26214400000000)]

def minusWeights0520 : Fin 11 → ℚ := ![(125290719/52428800000000), (125290719/5242880000000), (1127616471/10485760000000), (375872157/1310720000000), (2618817099/5242880000000), (7709251297/13107200000000), (2446987339/5242880000000), (314371213/1310720000000), (3785627523/52428800000000), (1268494897/131072000000000), 0]

theorem checked0520 :
    (∀ i, 0 ≤ plusWeights0520 i) ∧
    (∀ i, 0 ≤ minusWeights0520 i) ∧
    (∀ i, plusCoefficients coefficients0520 upper0520 i = powerCoefficients10 plusWeights0520 i) ∧
    (∀ i, minusCoefficients coefficients0520 upper0520 i = powerCoefficients10 minusWeights0520 i) := by
  decide +kernel

theorem bound0520 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0520 g| ≤ (upper0520 : ℝ) :=
  abs_of_coefficients coefficients0520 upper0520 powerCoefficients10 plusWeights0520 minusWeights0520
    checked0520.1 checked0520.2.1 checked0520.2.2.1 checked0520.2.2.2
    (power_identity10 plusWeights0520) (power_identity10 minusWeights0520) g hg hmax

def envelope0520 : Envelope := ⟨coefficients0520, upper0520, bound0520⟩

def coefficients0521 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/128), (-1/512), (35/512), (189/4096), (4225/32768), (5085/65536), (2075/32768)]

def upper0521 : ℚ := (392981/163840000000)

def plusWeights0521 : Fin 11 → ℚ := ![(392981/163840000000), (392981/16384000000), (3536829/32768000000), (1178943/4096000000), (8291001/16384000000), (25333003/40960000000), (8828121/16384000000), (13712819/40960000000), (93927297/655360000000), (501225057/13107200000000), (392981/81920000000)]

def minusWeights0521 : Fin 11 → ℚ := ![(392981/163840000000), (392981/16384000000), (3536829/32768000000), (1178943/4096000000), (8214201/16384000000), (24182603/40960000000), (7677081/16384000000), (9866041/40960000000), (47545863/655360000000), (127544543/13107200000000), 0]

theorem checked0521 :
    (∀ i, 0 ≤ plusWeights0521 i) ∧
    (∀ i, 0 ≤ minusWeights0521 i) ∧
    (∀ i, plusCoefficients coefficients0521 upper0521 i = powerCoefficients10 plusWeights0521 i) ∧
    (∀ i, minusCoefficients coefficients0521 upper0521 i = powerCoefficients10 minusWeights0521 i) := by
  decide +kernel

theorem bound0521 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0521 g| ≤ (upper0521 : ℝ) :=
  abs_of_coefficients coefficients0521 upper0521 powerCoefficients10 plusWeights0521 minusWeights0521
    checked0521.1 checked0521.2.1 checked0521.2.2.1 checked0521.2.2.2
    (power_identity10 plusWeights0521) (power_identity10 minusWeights0521) g hg hmax

def envelope0521 : Envelope := ⟨coefficients0521, upper0521, bound0521⟩

def coefficients0522 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/128), (9/512), (119/2048), (151/4096), (2323/32768), (2971/65536), (3775/131072)]

def upper0522 : ℚ := (676876879/262144000000000)

def plusWeights0522 : Fin 11 → ℚ := ![(676876879/262144000000000), (676876879/26214400000000), (6091891911/52428800000000), (2030630637/6553600000000), (14275854459/26214400000000), (43576363377/65536000000000), (15160577659/26214400000000), (2350897997/6553600000000), (8046147319/52428800000000), (5374889777/131072000000000), (676876879/131072000000000)]

def minusWeights0522 : Fin 11 → ℚ := ![(676876879/262144000000000), (676876879/26214400000000), (6091891911/52428800000000), (2030630637/6553600000000), (14152974459/26214400000000), (41710123377/65536000000000), (13268251259/26214400000000), (1710363277/6553600000000), (4137636503/52428800000000), (1393879013/131072000000000), 0]

theorem checked0522 :
    (∀ i, 0 ≤ plusWeights0522 i) ∧
    (∀ i, 0 ≤ minusWeights0522 i) ∧
    (∀ i, plusCoefficients coefficients0522 upper0522 i = powerCoefficients10 plusWeights0522 i) ∧
    (∀ i, minusCoefficients coefficients0522 upper0522 i = powerCoefficients10 minusWeights0522 i) := by
  decide +kernel

theorem bound0522 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0522 g| ≤ (upper0522 : ℝ) :=
  abs_of_coefficients coefficients0522 upper0522 powerCoefficients10 plusWeights0522 minusWeights0522
    checked0522.1 checked0522.2.1 checked0522.2.2.1 checked0522.2.2.2
    (power_identity10 plusWeights0522) (power_identity10 minusWeights0522) g hg hmax

def envelope0522 : Envelope := ⟨coefficients0522, upper0522, bound0522⟩

def coefficients0523 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-21/256), (-5/64), (-495/2048), (-107/512), (-727/4096), (-247/4096)]

def upper0523 : ℚ := (90116883/40960000000000)

def plusWeights0523 : Fin 11 → ℚ := ![(90116883/40960000000000), (90116883/4096000000000), (811051947/8192000000000), (270350649/1024000000000), (1905254543/4096000000000), (5860963629/10240000000000), (2067334543/4096000000000), (325605899/1024000000000), (1123400827/8192000000000), (37130509/1024000000000), (90116883/20480000000000)]

def minusWeights0523 : Fin 11 → ℚ := ![(90116883/40960000000000), (90116883/4096000000000), (811051947/8192000000000), (270350649/1024000000000), (1879654543/4096000000000), (5493763629/10240000000000), (1717574543/4096000000000), (215095399/1024000000000), (498703067/8192000000000), (3171173/409600000000), 0]

theorem checked0523 :
    (∀ i, 0 ≤ plusWeights0523 i) ∧
    (∀ i, 0 ≤ minusWeights0523 i) ∧
    (∀ i, plusCoefficients coefficients0523 upper0523 i = powerCoefficients10 plusWeights0523 i) ∧
    (∀ i, minusCoefficients coefficients0523 upper0523 i = powerCoefficients10 minusWeights0523 i) := by
  decide +kernel

theorem bound0523 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0523 g| ≤ (upper0523 : ℝ) :=
  abs_of_coefficients coefficients0523 upper0523 powerCoefficients10 plusWeights0523 minusWeights0523
    checked0523.1 checked0523.2.1 checked0523.2.2.1 checked0523.2.2.2
    (power_identity10 plusWeights0523) (power_identity10 minusWeights0523) g hg hmax

def envelope0523 : Envelope := ⟨coefficients0523, upper0523, bound0523⟩

def coefficients0524 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-21/256), (-35/512), (-543/2048), (-245/1024), (-1703/8192), (-1171/16384)]

def upper0524 : ℚ := (361628769/163840000000000)

def plusWeights0524 : Fin 11 → ℚ := ![(361628769/163840000000000), (361628769/16384000000000), (3254658921/32768000000000), (1084886307/4096000000000), (7645404149/16384000000000), (23517012447/40960000000000), (8293884149/16384000000000), (1306057707/4096000000000), (4505734121/32768000000000), (595763763/16384000000000), (361628769/81920000000000)]

def minusWeights0524 : Fin 11 → ℚ := ![(361628769/163840000000000), (361628769/16384000000000), (3254658921/32768000000000), (1084886307/4096000000000), (7543004149/16384000000000), (22048212447/40960000000000), (6894524149/16384000000000), (863714907/4096000000000), (2003583721/32768000000000), (5099751/655360000000), 0]

theorem checked0524 :
    (∀ i, 0 ≤ plusWeights0524 i) ∧
    (∀ i, 0 ≤ minusWeights0524 i) ∧
    (∀ i, plusCoefficients coefficients0524 upper0524 i = powerCoefficients10 plusWeights0524 i) ∧
    (∀ i, minusCoefficients coefficients0524 upper0524 i = powerCoefficients10 minusWeights0524 i) := by
  decide +kernel

theorem bound0524 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0524 g| ≤ (upper0524 : ℝ) :=
  abs_of_coefficients coefficients0524 upper0524 powerCoefficients10 plusWeights0524 minusWeights0524
    checked0524.1 checked0524.2.1 checked0524.2.2.1 checked0524.2.2.2
    (power_identity10 plusWeights0524) (power_identity10 minusWeights0524) g hg hmax

def envelope0524 : Envelope := ⟨coefficients0524, upper0524, bound0524⟩

def coefficients0525 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-21/256), (-35/512), (-961/4096), (-465/2048), (-3131/16384), (-2117/32768)]

def upper0525 : ℚ := (724303263/327680000000000)

def plusWeights0525 : Fin 11 → ℚ := ![(724303263/327680000000000), (724303263/32768000000000), (6518729367/65536000000000), (2172909789/8192000000000), (15312768523/32768000000000), (47099905569/81920000000000), (16609728523/32768000000000), (2615277589/8192000000000), (9021487767/65536000000000), (1192881801/32768000000000), (724303263/163840000000000)]

def minusWeights0525 : Fin 11 → ℚ := ![(724303263/327680000000000), (724303263/32768000000000), (6518729367/65536000000000), (2172909789/8192000000000), (15107968523/32768000000000), (44162305569/81920000000000), (13811008523/32768000000000), (1730541989/8192000000000), (4015970967/65536000000000), (10228989/1310720000000), 0]

theorem checked0525 :
    (∀ i, 0 ≤ plusWeights0525 i) ∧
    (∀ i, 0 ≤ minusWeights0525 i) ∧
    (∀ i, plusCoefficients coefficients0525 upper0525 i = powerCoefficients10 plusWeights0525 i) ∧
    (∀ i, minusCoefficients coefficients0525 upper0525 i = powerCoefficients10 minusWeights0525 i) := by
  decide +kernel

theorem bound0525 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0525 g| ≤ (upper0525 : ℝ) :=
  abs_of_coefficients coefficients0525 upper0525 powerCoefficients10 plusWeights0525 minusWeights0525
    checked0525.1 checked0525.2.1 checked0525.2.2.1 checked0525.2.2.2
    (power_identity10 plusWeights0525) (power_identity10 minusWeights0525) g hg hmax

def envelope0525 : Envelope := ⟨coefficients0525, upper0525, bound0525⟩

def coefficients0526 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-19/256), (-21/256), (-93/512), (-247/2048), (-1345/16384), (-875/32768)]

def upper0526 : ℚ := (29901801/13107200000000)

def plusWeights0526 : Fin 11 → ℚ := ![(29901801/13107200000000), (29901801/1310720000000), (269116209/2621440000000), (89705403/327680000000), (632033821/1310720000000), (1942821463/3276800000000), (684406301/1310720000000), (107639931/327680000000), (1855519797/13107200000000), (245545139/6553600000000), (29901801/6553600000000)]

def minusWeights0526 : Fin 11 → ℚ := ![(29901801/13107200000000), (29901801/1310720000000), (269116209/2621440000000), (89705403/327680000000), (623841821/1310720000000), (1824805463/3276800000000), (571469341/1310720000000), (574167/2621440000), (835642293/13107200000000), (53472871/6553600000000), 0]

theorem checked0526 :
    (∀ i, 0 ≤ plusWeights0526 i) ∧
    (∀ i, 0 ≤ minusWeights0526 i) ∧
    (∀ i, plusCoefficients coefficients0526 upper0526 i = powerCoefficients10 plusWeights0526 i) ∧
    (∀ i, minusCoefficients coefficients0526 upper0526 i = powerCoefficients10 minusWeights0526 i) := by
  decide +kernel

theorem bound0526 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0526 g| ≤ (upper0526 : ℝ) :=
  abs_of_coefficients coefficients0526 upper0526 powerCoefficients10 plusWeights0526 minusWeights0526
    checked0526.1 checked0526.2.1 checked0526.2.2.1 checked0526.2.2.2
    (power_identity10 plusWeights0526) (power_identity10 minusWeights0526) g hg hmax

def envelope0526 : Envelope := ⟨coefficients0526, upper0526, bound0526⟩

def coefficients0527 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-15/256), (-15/256), (-491/4096), (-89/1024), (-715/16384), (-375/32768)]

def upper0527 : ℚ := (32342901/13107200000000)

def plusWeights0527 : Fin 11 → ℚ := ![(32342901/13107200000000), (32342901/1310720000000), (291086109/2621440000000), (97028703/327680000000), (683296921/1310720000000), (2097122763/3276800000000), (736724121/1310720000000), (4620319/13107200000), (1987939793/13107200000000), (263611147/6553600000000), (32342901/6553600000000)]

def minusWeights0527 : Fin 11 → ℚ := ![(32342901/13107200000000), (32342901/1310720000000), (291086109/2621440000000), (97028703/327680000000), (675104921/1310720000000), (1978082763/3276800000000), (621677721/1310720000000), (78549431/327680000000), (922921297/13107200000000), (59817863/6553600000000), 0]

theorem checked0527 :
    (∀ i, 0 ≤ plusWeights0527 i) ∧
    (∀ i, 0 ≤ minusWeights0527 i) ∧
    (∀ i, plusCoefficients coefficients0527 upper0527 i = powerCoefficients10 plusWeights0527 i) ∧
    (∀ i, minusCoefficients coefficients0527 upper0527 i = powerCoefficients10 minusWeights0527 i) := by
  decide +kernel

theorem bound0527 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0527 g| ≤ (upper0527 : ℝ) :=
  abs_of_coefficients coefficients0527 upper0527 powerCoefficients10 plusWeights0527 minusWeights0527
    checked0527.1 checked0527.2.1 checked0527.2.2.1 checked0527.2.2.2
    (power_identity10 plusWeights0527) (power_identity10 minusWeights0527) g hg hmax

def envelope0527 : Envelope := ⟨coefficients0527, upper0527, bound0527⟩

def coefficients0528 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-13/256), (39/1024), (281/4096), (3915/32768), (3655/65536), (15445/524288)]

def upper0528 : ℚ := (2792763969/1048576000000000)

def plusWeights0528 : Fin 11 → ℚ := ![(2792763969/1048576000000000), (2792763969/104857600000000), (25134875721/209715200000000), (8378291907/26214400000000), (58975723349/104857600000000), (180726210047/262144000000000), (63300996949/104857600000000), (9887745347/26214400000000), (33952805641/209715200000000), (4510992857/104857600000000), (2792763969/524288000000000)]

def minusWeights0528 : Fin 11 → ℚ := ![(2792763969/1048576000000000), (2792763969/104857600000000), (25134875721/209715200000000), (8378291907/26214400000000), (58320363349/104857600000000), (171162050047/262144000000000), (53995089749/104857600000000), (6868838467/26214400000000), (16316945801/209715200000000), (1074535081/104857600000000), 0]

theorem checked0528 :
    (∀ i, 0 ≤ plusWeights0528 i) ∧
    (∀ i, 0 ≤ minusWeights0528 i) ∧
    (∀ i, plusCoefficients coefficients0528 upper0528 i = powerCoefficients10 plusWeights0528 i) ∧
    (∀ i, minusCoefficients coefficients0528 upper0528 i = powerCoefficients10 minusWeights0528 i) := by
  decide +kernel

theorem bound0528 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0528 g| ≤ (upper0528 : ℝ) :=
  abs_of_coefficients coefficients0528 upper0528 powerCoefficients10 plusWeights0528 minusWeights0528
    checked0528.1 checked0528.2.1 checked0528.2.2.1 checked0528.2.2.2
    (power_identity10 plusWeights0528) (power_identity10 minusWeights0528) g hg hmax

def envelope0528 : Envelope := ⟨coefficients0528, upper0528, bound0528⟩

def coefficients0529 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-19/512), (-39/1024), (-1095/8192), (-255/2048), (-653/8192), (-193/8192)]

def upper0529 : ℚ := (221276277/81920000000000)

def plusWeights0529 : Fin 11 → ℚ := ![(221276277/81920000000000), (221276277/8192000000000), (1991486493/16384000000000), (663828831/2048000000000), (4672401817/8192000000000), (14316805451/20480000000000), (5015289817/8192000000000), (48993091/128000000000), (2694265093/16384000000000), (89519681/2048000000000), (221276277/40960000000000)]

def minusWeights0529 : Fin 11 → ℚ := ![(221276277/81920000000000), (221276277/8192000000000), (1991486493/16384000000000), (663828831/2048000000000), (4621201817/8192000000000), (13564005451/20480000000000), (4278313817/8192000000000), (271884103/1024000000000), (1288707893/16384000000000), (8447383/819200000000), 0]

theorem checked0529 :
    (∀ i, 0 ≤ plusWeights0529 i) ∧
    (∀ i, 0 ≤ minusWeights0529 i) ∧
    (∀ i, plusCoefficients coefficients0529 upper0529 i = powerCoefficients10 plusWeights0529 i) ∧
    (∀ i, minusCoefficients coefficients0529 upper0529 i = powerCoefficients10 minusWeights0529 i) := by
  decide +kernel

theorem bound0529 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0529 g| ≤ (upper0529 : ℝ) :=
  abs_of_coefficients coefficients0529 upper0529 powerCoefficients10 plusWeights0529 minusWeights0529
    checked0529.1 checked0529.2.1 checked0529.2.2.1 checked0529.2.2.2
    (power_identity10 plusWeights0529) (power_identity10 minusWeights0529) g hg hmax

def envelope0529 : Envelope := ⟨coefficients0529, upper0529, bound0529⟩

def coefficients0530 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-17/512), (-41/1024), (-921/8192), (-373/4096), (-1485/32768), (-775/65536)]

def upper0530 : ℚ := (71846589/26214400000000)

def plusWeights0530 : Fin 11 → ℚ := ![(71846589/26214400000000), (71846589/2621440000000), (646619301/5242880000000), (215539767/655360000000), (1516970369/2621440000000), (4647039107/6553600000000), (1627201409/2621440000000), (254211439/655360000000), (4367650873/26214400000000), (580667199/13107200000000), (71846589/13107200000000)]

def minusWeights0530 : Fin 11 → ℚ := ![(71846589/26214400000000), (71846589/2621440000000), (646619301/5242880000000), (215539767/655360000000), (1500586369/2621440000000), (4405631107/6553600000000), (1390355329/2621440000000), (35373619/131072000000), (2098542137/26214400000000), (137798691/13107200000000), 0]

theorem checked0530 :
    (∀ i, 0 ≤ plusWeights0530 i) ∧
    (∀ i, 0 ≤ minusWeights0530 i) ∧
    (∀ i, plusCoefficients coefficients0530 upper0530 i = powerCoefficients10 plusWeights0530 i) ∧
    (∀ i, minusCoefficients coefficients0530 upper0530 i = powerCoefficients10 minusWeights0530 i) := by
  decide +kernel

theorem bound0530 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0530 g| ≤ (upper0530 : ℝ) :=
  abs_of_coefficients coefficients0530 upper0530 powerCoefficients10 plusWeights0530 minusWeights0530
    checked0530.1 checked0530.2.1 checked0530.2.2.1 checked0530.2.2.2
    (power_identity10 plusWeights0530) (power_identity10 minusWeights0530) g hg hmax

def envelope0530 : Envelope := ⟨coefficients0530, upper0530, bound0530⟩

def coefficients0531 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (-9/512), (-27/1024), (-615/8192), (-15/256), (-1945/65536), (-1025/131072)]

def upper0531 : ℚ := (152815683/52428800000000)

def plusWeights0531 : Fin 11 → ℚ := ![(152815683/52428800000000), (152815683/5242880000000), (1375341147/10485760000000), (458447049/1310720000000), (3225513343/5242880000000), (9870844029/13107200000000), (3450143103/5242880000000), (537914969/1310720000000), (1846527963/10485760000000), (1229171717/26214400000000), (152815683/26214400000000)]

def minusWeights0531 : Fin 11 → ℚ := ![(152815683/52428800000000), (152815683/5242880000000), (1375341147/10485760000000), (458447049/1310720000000), (3192745343/5242880000000), (9383932029/13107200000000), (2968115583/5242880000000), (378979129/1310720000000), (904154331/10485760000000), (298985113/26214400000000), 0]

theorem checked0531 :
    (∀ i, 0 ≤ plusWeights0531 i) ∧
    (∀ i, 0 ≤ minusWeights0531 i) ∧
    (∀ i, plusCoefficients coefficients0531 upper0531 i = powerCoefficients10 plusWeights0531 i) ∧
    (∀ i, minusCoefficients coefficients0531 upper0531 i = powerCoefficients10 minusWeights0531 i) := by
  decide +kernel

theorem bound0531 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0531 g| ≤ (upper0531 : ℝ) :=
  abs_of_coefficients coefficients0531 upper0531 powerCoefficients10 plusWeights0531 minusWeights0531
    checked0531.1 checked0531.2.1 checked0531.2.2.1 checked0531.2.2.2
    (power_identity10 plusWeights0531) (power_identity10 minusWeights0531) g hg hmax

def envelope0531 : Envelope := ⟨coefficients0531, upper0531, bound0531⟩

def coefficients0532 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (9/128), (81/1024), (321/8192), (31/1024), (129/4096), (65/8192)]

def upper0532 : ℚ := (64085689/16384000000000)

def plusWeights0532 : Fin 11 → ℚ := ![(64085689/16384000000000), (64085689/1638400000000), (576771201/3276800000000), (192257067/409600000000), (1350919469/1638400000000), (4117078407/4096000000000), (1428489069/1638400000000), (13804267/25600000000), (755005913/3276800000000), (505521963/8192000000000), (64085689/8192000000000)]

def minusWeights0532 : Fin 11 → ℚ := ![(64085689/16384000000000), (64085689/1638400000000), (576771201/3276800000000), (192257067/409600000000), (1340679469/1638400000000), (3957718407/4096000000000), (1263109869/1638400000000), (81822931/204800000000), (398536489/3276800000000), (135334927/8192000000000), 0]

theorem checked0532 :
    (∀ i, 0 ≤ plusWeights0532 i) ∧
    (∀ i, 0 ≤ minusWeights0532 i) ∧
    (∀ i, plusCoefficients coefficients0532 upper0532 i = powerCoefficients10 plusWeights0532 i) ∧
    (∀ i, minusCoefficients coefficients0532 upper0532 i = powerCoefficients10 minusWeights0532 i) := by
  decide +kernel

theorem bound0532 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0532 g| ≤ (upper0532 : ℝ) :=
  abs_of_coefficients coefficients0532 upper0532 powerCoefficients10 plusWeights0532 minusWeights0532
    checked0532.1 checked0532.2.1 checked0532.2.2.1 checked0532.2.2.2
    (power_identity10 plusWeights0532) (power_identity10 minusWeights0532) g hg hmax

def envelope0532 : Envelope := ⟨coefficients0532, upper0532, bound0532⟩

def coefficients0533 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/32), (23/256), (63/512), (179/2048), (269/4096), (249/4096), (245/16384)]

def upper0533 : ℚ := (136181961/32768000000000)

def plusWeights0533 : Fin 11 → ℚ := ![(136181961/32768000000000), (136181961/3276800000000), (1225637649/6553600000000), (408545883/819200000000), (2870061181/3276800000000), (8740423543/8192000000000), (3028544381/3276800000000), (467516243/819200000000), (1596732193/6553600000000), (1070225921/16384000000000), (136181961/16384000000000)]

def minusWeights0533 : Fin 11 → ℚ := ![(136181961/32768000000000), (136181961/3276800000000), (1225637649/6553600000000), (408545883/819200000000), (2849581181/3276800000000), (8418503543/8192000000000), (2691097981/3276800000000), (349575523/819200000000), (170908621/1310720000000), (291593689/16384000000000), 0]

theorem checked0533 :
    (∀ i, 0 ≤ plusWeights0533 i) ∧
    (∀ i, 0 ≤ minusWeights0533 i) ∧
    (∀ i, plusCoefficients coefficients0533 upper0533 i = powerCoefficients10 plusWeights0533 i) ∧
    (∀ i, minusCoefficients coefficients0533 upper0533 i = powerCoefficients10 minusWeights0533 i) := by
  decide +kernel

theorem bound0533 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0533 g| ≤ (upper0533 : ℝ) :=
  abs_of_coefficients coefficients0533 upper0533 powerCoefficients10 plusWeights0533 minusWeights0533
    checked0533.1 checked0533.2.1 checked0533.2.2.1 checked0533.2.2.2
    (power_identity10 plusWeights0533) (power_identity10 minusWeights0533) g hg hmax

def envelope0533 : Envelope := ⟨coefficients0533, upper0533, bound0533⟩

def coefficients0534 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/64), (-1/256), (3/64), (141/4096), (3231/16384), (4207/32768), (22695/131072)]

def upper0534 : ℚ := (246461111/52428800000000)

def plusWeights0534 : Fin 11 → ℚ := ![(246461111/52428800000000), (246461111/5242880000000), (2218149999/10485760000000), (739383333/1310720000000), (5200259331/5242880000000), (15895177993/13107200000000), (5543545091/5242880000000), (172400321/262144000000), (14772060427/52428800000000), (9848791163/131072000000000), (246461111/26214400000000)]

def minusWeights0534 : Fin 11 → ℚ := ![(246461111/52428800000000), (246461111/5242880000000), (2218149999/10485760000000), (739383333/1310720000000), (5151107331/5242880000000), (15158921993/13107200000000), (4807821571/5242880000000), (616765061/1310720000000), (7409439563/52428800000000), (2474264387/131072000000000), 0]

theorem checked0534 :
    (∀ i, 0 ≤ plusWeights0534 i) ∧
    (∀ i, 0 ≤ minusWeights0534 i) ∧
    (∀ i, plusCoefficients coefficients0534 upper0534 i = powerCoefficients10 plusWeights0534 i) ∧
    (∀ i, minusCoefficients coefficients0534 upper0534 i = powerCoefficients10 minusWeights0534 i) := by
  decide +kernel

theorem bound0534 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0534 g| ≤ (upper0534 : ℝ) :=
  abs_of_coefficients coefficients0534 upper0534 powerCoefficients10 plusWeights0534 minusWeights0534
    checked0534.1 checked0534.2.1 checked0534.2.2.1 checked0534.2.2.2
    (power_identity10 plusWeights0534) (power_identity10 minusWeights0534) g hg hmax

def envelope0534 : Envelope := ⟨coefficients0534, upper0534, bound0534⟩

def coefficients0535 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/64), (-1/256), (227/2048), (399/4096), (6979/32768), (8143/65536), (27705/262144)]

def upper0535 : ℚ := (100061061/20971520000000)

def plusWeights0535 : Fin 11 → ℚ := ![(100061061/20971520000000), (100061061/2097152000000), (900549549/4194304000000), (300183183/524288000000), (2111112681/2097152000000), (6451098043/5242880000000), (2248561129/2097152000000), (1746839691/2621440000000), (29918600773/104857600000000), (19954266637/262144000000000), (100061061/10485760000000)]

def minusWeights0535 : Fin 11 → ℚ := ![(100061061/20971520000000), (100061061/2097152000000), (900549549/4194304000000), (300183183/524288000000), (2091451881/2097152000000), (6156595643/5242880000000), (1954003433/2097152000000), (1254992139/2621440000000), (15108876677/104857600000000), (5060998613/262144000000000), 0]

theorem checked0535 :
    (∀ i, 0 ≤ plusWeights0535 i) ∧
    (∀ i, 0 ≤ minusWeights0535 i) ∧
    (∀ i, plusCoefficients coefficients0535 upper0535 i = powerCoefficients10 plusWeights0535 i) ∧
    (∀ i, minusCoefficients coefficients0535 upper0535 i = powerCoefficients10 minusWeights0535 i) := by
  decide +kernel

theorem bound0535 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0535 g| ≤ (upper0535 : ℝ) :=
  abs_of_coefficients coefficients0535 upper0535 powerCoefficients10 plusWeights0535 minusWeights0535
    checked0535.1 checked0535.2.1 checked0535.2.2.1 checked0535.2.2.2
    (power_identity10 plusWeights0535) (power_identity10 minusWeights0535) g hg hmax

def envelope0535 : Envelope := ⟨coefficients0535, upper0535, bound0535⟩

def coefficients0536 : Fin 11 → ℚ := ![0, 0, 0, 0, (3/64), (13/512), (221/2048), (271/4096), (6047/32768), (7979/65536), (27005/262144)]

def upper0536 : ℚ := (2651801553/524288000000000)

def plusWeights0536 : Fin 11 → ℚ := ![(2651801553/524288000000000), (2651801553/52428800000000), (23866213977/104857600000000), (7955404659/13107200000000), (55933592613/52428800000000), (170783177839/131072000000000), (59446450213/52428800000000), (9223228979/13107200000000), (31575419961/104857600000000), (21083962401/262144000000000), (2651801553/262144000000000)]

def minusWeights0536 : Fin 11 → ℚ := ![(2651801553/524288000000000), (2651801553/52428800000000), (23866213977/104857600000000), (7955404659/13107200000000), (55442072613/52428800000000), (163343817839/131072000000000), (51929215013/52428800000000), (6687580339/13107200000000), (16157007993/104857600000000), (5434053129/262144000000000), 0]

theorem checked0536 :
    (∀ i, 0 ≤ plusWeights0536 i) ∧
    (∀ i, 0 ≤ minusWeights0536 i) ∧
    (∀ i, plusCoefficients coefficients0536 upper0536 i = powerCoefficients10 plusWeights0536 i) ∧
    (∀ i, minusCoefficients coefficients0536 upper0536 i = powerCoefficients10 minusWeights0536 i) := by
  decide +kernel

theorem bound0536 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0536 g| ≤ (upper0536 : ℝ) :=
  abs_of_coefficients coefficients0536 upper0536 powerCoefficients10 plusWeights0536 minusWeights0536
    checked0536.1 checked0536.2.1 checked0536.2.2.1 checked0536.2.2.2
    (power_identity10 plusWeights0536) (power_identity10 minusWeights0536) g hg hmax

def envelope0536 : Envelope := ⟨coefficients0536, upper0536, bound0536⟩

def coefficients0537 : Fin 11 → ℚ := ![0, 0, 0, 0, (7/128), (-25/256), (175/2048), (139/1024), (533/2048), (2089/16384), (10565/131072)]

def upper0537 : ℚ := (1204276177/262144000000000)

def plusWeights0537 : Fin 11 → ℚ := ![(1204276177/262144000000000), (1204276177/26214400000000), (10838485593/52428800000000), (3612828531/6553600000000), (25433159717/26214400000000), (77955799151/65536000000000), (27314439717/26214400000000), (4267957491/6553600000000), (14656437081/52428800000000), (9733017437/131072000000000), (1204276177/131072000000000)]

def minusWeights0537 : Fin 11 → ℚ := ![(1204276177/262144000000000), (1204276177/26214400000000), (10838485593/52428800000000), (3612828531/6553600000000), (25146439717/26214400000000), (73782999151/65536000000000), (23265159717/26214400000000), (2957699571/6553600000000), (1404106821/10485760000000), (2309744333/131072000000000), 0]

theorem checked0537 :
    (∀ i, 0 ≤ plusWeights0537 i) ∧
    (∀ i, 0 ≤ minusWeights0537 i) ∧
    (∀ i, plusCoefficients coefficients0537 upper0537 i = powerCoefficients10 plusWeights0537 i) ∧
    (∀ i, minusCoefficients coefficients0537 upper0537 i = powerCoefficients10 minusWeights0537 i) := by
  decide +kernel

theorem bound0537 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0537 g| ≤ (upper0537 : ℝ) :=
  abs_of_coefficients coefficients0537 upper0537 powerCoefficients10 plusWeights0537 minusWeights0537
    checked0537.1 checked0537.2.1 checked0537.2.2.1 checked0537.2.2.2
    (power_identity10 plusWeights0537) (power_identity10 minusWeights0537) g hg hmax

def envelope0537 : Envelope := ⟨coefficients0537, upper0537, bound0537⟩

def coefficients0538 : Fin 11 → ℚ := ![0, 0, 0, 0, (7/128), (-25/256), (201/2048), (247/2048), (4725/16384), (4395/32768), (1275/16384)]

def upper0538 : ℚ := (3018207/655360000000)

def plusWeights0538 : Fin 11 → ℚ := ![(3018207/655360000000), (3018207/65536000000), (27163863/131072000000), (9054621/16384000000), (63740747/65536000000), (195363041/163840000000), (68444779/65536000000), (53466253/81920000000), (183590837/655360000000), (487709299/6553600000000), (3018207/327680000000)]

def minusWeights0538 : Fin 11 → ℚ := ![(3018207/655360000000), (3018207/65536000000), (27163863/131072000000), (9054621/16384000000), (63023947/65536000000), (184931041/163840000000), (11663983/13107200000), (37079957/81920000000), (88047793/655360000000), (115932101/6553600000000), 0]

theorem checked0538 :
    (∀ i, 0 ≤ plusWeights0538 i) ∧
    (∀ i, 0 ≤ minusWeights0538 i) ∧
    (∀ i, plusCoefficients coefficients0538 upper0538 i = powerCoefficients10 plusWeights0538 i) ∧
    (∀ i, minusCoefficients coefficients0538 upper0538 i = powerCoefficients10 minusWeights0538 i) := by
  decide +kernel

theorem bound0538 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0538 g| ≤ (upper0538 : ℝ) :=
  abs_of_coefficients coefficients0538 upper0538 powerCoefficients10 plusWeights0538 minusWeights0538
    checked0538.1 checked0538.2.1 checked0538.2.2.1 checked0538.2.2.2
    (power_identity10 plusWeights0538) (power_identity10 minusWeights0538) g hg hmax

def envelope0538 : Envelope := ⟨coefficients0538, upper0538, bound0538⟩

def coefficients0539 : Fin 11 → ℚ := ![0, 0, 0, 0, (7/128), (-5/128), (79/1024), (205/2048), (5369/32768), (4593/65536), (7245/262144)]

def upper0539 : ℚ := (2708993233/524288000000000)

def plusWeights0539 : Fin 11 → ℚ := ![(2708993233/524288000000000), (2708993233/52428800000000), (24380939097/104857600000000), (8126979699/13107200000000), (57175577893/52428800000000), (174916173679/131072000000000), (61091302693/52428800000000), (9513555699/13107200000000), (6524959461/20971520000000), (21724211577/262144000000000), (2708993233/262144000000000)]

def minusWeights0539 : Fin 11 → ℚ := ![(2708993233/524288000000000), (2708993233/52428800000000), (24380939097/104857600000000), (8126979699/13107200000000), (56602137893/52428800000000), (166416973679/131072000000000), (52686413093/52428800000000), (6740403699/13107200000000), (16137080889/104857600000000), (5365720753/262144000000000), 0]

theorem checked0539 :
    (∀ i, 0 ≤ plusWeights0539 i) ∧
    (∀ i, 0 ≤ minusWeights0539 i) ∧
    (∀ i, plusCoefficients coefficients0539 upper0539 i = powerCoefficients10 plusWeights0539 i) ∧
    (∀ i, minusCoefficients coefficients0539 upper0539 i = powerCoefficients10 minusWeights0539 i) := by
  decide +kernel

theorem bound0539 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0539 g| ≤ (upper0539 : ℝ) :=
  abs_of_coefficients coefficients0539 upper0539 powerCoefficients10 plusWeights0539 minusWeights0539
    checked0539.1 checked0539.2.1 checked0539.2.2.1 checked0539.2.2.2
    (power_identity10 plusWeights0539) (power_identity10 minusWeights0539) g hg hmax

def envelope0539 : Envelope := ⟨coefficients0539, upper0539, bound0539⟩

def coefficients0540 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/16), (77/512), (181/1024), (195/2048), (55/512), (55/512), (55/2048)]

def upper0540 : ℚ := (32527851/4096000000000)

def plusWeights0540 : Fin 11 → ℚ := ![(32527851/4096000000000), (32527851/409600000000), (292750659/819200000000), (97583553/102400000000), (685644871/409600000000), (2089194613/1024000000000), (724637271/409600000000), (27343/25000000), (382763739/819200000000), (2050803/16384000000), (32527851/2048000000000)]

def minusWeights0540 : Fin 11 → ℚ := ![(32527851/4096000000000), (32527851/409600000000), (292750659/819200000000), (97583553/102400000000), (680524871/409600000000), (2009314613/1024000000000), (641532471/409600000000), (41585089/51200000000), (202737579/819200000000), (13785627/409600000000), 0]

theorem checked0540 :
    (∀ i, 0 ≤ plusWeights0540 i) ∧
    (∀ i, 0 ≤ minusWeights0540 i) ∧
    (∀ i, plusCoefficients coefficients0540 upper0540 i = powerCoefficients10 plusWeights0540 i) ∧
    (∀ i, minusCoefficients coefficients0540 upper0540 i = powerCoefficients10 minusWeights0540 i) := by
  decide +kernel

theorem bound0540 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0540 g| ≤ (upper0540 : ℝ) :=
  abs_of_coefficients coefficients0540 upper0540 powerCoefficients10 plusWeights0540 minusWeights0540
    checked0540.1 checked0540.2.1 checked0540.2.2.1 checked0540.2.2.2
    (power_identity10 plusWeights0540) (power_identity10 minusWeights0540) g hg hmax

def envelope0540 : Envelope := ⟨coefficients0540, upper0540, bound0540⟩

def coefficients0541 : Fin 11 → ℚ := ![0, 0, 0, 0, (1/16), (23/128), (45/256), (227/2048), (153/1024), (69/512), (135/4096)]

def upper0541 : ℚ := (67464171/8192000000000)

def plusWeights0541 : Fin 11 → ℚ := ![(67464171/8192000000000), (67464171/819200000000), (607177539/1638400000000), (202392513/204800000000), (1421867591/819200000000), (4330722773/2048000000000), (1501051591/819200000000), (231818783/204800000000), (792002467/1638400000000), (530749847/4096000000000), (67464171/4096000000000)]

def minusWeights0541 : Fin 11 → ℚ := ![(67464171/8192000000000), (67464171/819200000000), (607177539/1638400000000), (202392513/204800000000), (1411627591/819200000000), (4169762773/2048000000000), (1332443591/819200000000), (172966243/204800000000), (422352611/1638400000000), (143891863/4096000000000), 0]

theorem checked0541 :
    (∀ i, 0 ≤ plusWeights0541 i) ∧
    (∀ i, 0 ≤ minusWeights0541 i) ∧
    (∀ i, plusCoefficients coefficients0541 upper0541 i = powerCoefficients10 plusWeights0541 i) ∧
    (∀ i, minusCoefficients coefficients0541 upper0541 i = powerCoefficients10 minusWeights0541 i) := by
  decide +kernel

theorem bound0541 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0541 g| ≤ (upper0541 : ℝ) :=
  abs_of_coefficients coefficients0541 upper0541 powerCoefficients10 plusWeights0541 minusWeights0541
    checked0541.1 checked0541.2.1 checked0541.2.2.1 checked0541.2.2.2
    (power_identity10 plusWeights0541) (power_identity10 minusWeights0541) g hg hmax

def envelope0541 : Envelope := ⟨coefficients0541, upper0541, bound0541⟩

def coefficients0542 : Fin 11 → ℚ := ![0, 0, 0, (1/32), (3/32), (7/64), (5/64), (363/8192), (169/8192), (99/8192), (85/32768)]

def upper0542 : ℚ := (2739504729/65536000000000)

def plusWeights0542 : Fin 11 → ℚ := ![(2739504729/65536000000000), (2739504729/6553600000000), (24655542561/13107200000000), (8269714187/1638400000000), (59024639309/6553600000000), (184280317927/16384000000000), (65655551309/6553600000000), (10336153447/1638400000000), (7050004701/2621440000000), (22898613161/32768000000000), (2739504729/32768000000000)]

def minusWeights0542 : Fin 11 → ℚ := ![(2739504729/65536000000000), (2739504729/6553600000000), (24655542561/13107200000000), (8167314187/1638400000000), (56034559309/6553600000000), (160897277927/16384000000000), (49403647309/6553600000000), (6100874927/1638400000000), (14061061617/13107200000000), (4496434129/32768000000000), 0]

theorem checked0542 :
    (∀ i, 0 ≤ plusWeights0542 i) ∧
    (∀ i, 0 ≤ minusWeights0542 i) ∧
    (∀ i, plusCoefficients coefficients0542 upper0542 i = powerCoefficients10 plusWeights0542 i) ∧
    (∀ i, minusCoefficients coefficients0542 upper0542 i = powerCoefficients10 minusWeights0542 i) := by
  decide +kernel

theorem bound0542 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0542 g| ≤ (upper0542 : ℝ) :=
  abs_of_coefficients coefficients0542 upper0542 powerCoefficients10 plusWeights0542 minusWeights0542
    checked0542.1 checked0542.2.1 checked0542.2.2.1 checked0542.2.2.2
    (power_identity10 plusWeights0542) (power_identity10 minusWeights0542) g hg hmax

def envelope0542 : Envelope := ⟨coefficients0542, upper0542, bound0542⟩

def coefficients0543 : Fin 11 → ℚ := ![0, 0, 0, (1/32), (1/8), (97/512), (169/1024), (95/1024), (215/4096), (165/4096), (155/16384)]

def upper0543 : ℚ := (1501410551/32768000000000)

def plusWeights0543 : Fin 11 → ℚ := ![(1501410551/32768000000000), (1501410551/3276800000000), (13512694959/6553600000000), (4529831653/819200000000), (32287381571/3276800000000), (100594784713/8192000000000), (35759602371/3276800000000), (5621100053/819200000000), (19173130399/6553600000000), (2497268523/3276800000000), (1501410551/16384000000000)]

def minusWeights0543 : Fin 11 → ℚ := ![(1501410551/32768000000000), (1501410551/3276800000000), (13512694959/6553600000000), (4478631653/819200000000), (30771861571/3276800000000), (88582944713/8192000000000), (27299640771/3276800000000), (3387363253/819200000000), (7852259519/6553600000000), (505552579/3276800000000), 0]

theorem checked0543 :
    (∀ i, 0 ≤ plusWeights0543 i) ∧
    (∀ i, 0 ≤ minusWeights0543 i) ∧
    (∀ i, plusCoefficients coefficients0543 upper0543 i = powerCoefficients10 plusWeights0543 i) ∧
    (∀ i, minusCoefficients coefficients0543 upper0543 i = powerCoefficients10 minusWeights0543 i) := by
  decide +kernel

theorem bound0543 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0543 g| ≤ (upper0543 : ℝ) :=
  abs_of_coefficients coefficients0543 upper0543 powerCoefficients10 plusWeights0543 minusWeights0543
    checked0543.1 checked0543.2.1 checked0543.2.2.1 checked0543.2.2.2
    (power_identity10 plusWeights0543) (power_identity10 minusWeights0543) g hg hmax

def envelope0543 : Envelope := ⟨coefficients0543, upper0543, bound0543⟩

end BilayerDressed.CubicQuarticEnvelopes

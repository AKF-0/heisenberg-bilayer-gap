import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0576 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-21/512), (-33/1024), (-417/8192), (-141/4096), (-285/16384), (-75/16384)]

def upper0576 : ℚ := (2934933/6553600000000)

def plusWeights0576 : Fin 11 → ℚ := ![(2934933/6553600000000), (2934933/655360000000), (26414397/1310720000000), (8804799/163840000000), (61633593/655360000000), (184228779/1638400000000), (60268473/655360000000), (1622169/32768000000), (103822449/6553600000000), (934989/409600000000), 0]

def minusWeights0576 : Fin 11 → ℚ := ![(2934933/6553600000000), (2934933/655360000000), (26414397/1310720000000), (8804799/163840000000), (61633593/655360000000), (185572779/1638400000000), (62998713/655360000000), (9498753/163840000000), (160321521/6553600000000), (10934709/1638400000000), (2934933/3276800000000)]

theorem checked0576 :
    (∀ i, 0 ≤ plusWeights0576 i) ∧
    (∀ i, 0 ≤ minusWeights0576 i) ∧
    (∀ i, plusCoefficients coefficients0576 upper0576 i = powerCoefficients10 plusWeights0576 i) ∧
    (∀ i, minusCoefficients coefficients0576 upper0576 i = powerCoefficients10 minusWeights0576 i) := by
  decide +kernel

theorem bound0576 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0576 g| ≤ (upper0576 : ℝ) :=
  abs_of_coefficients coefficients0576 upper0576 powerCoefficients10 plusWeights0576 minusWeights0576
    checked0576.1 checked0576.2.1 checked0576.2.2.1 checked0576.2.2.2
    (power_identity10 plusWeights0576) (power_identity10 minusWeights0576) g hg hmax

def envelope0576 : Envelope := ⟨coefficients0576, upper0576, bound0576⟩

def coefficients0577 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-21/512), (-33/1024), (-377/8192), (-121/4096), (-15/1024), (-125/32768)]

def upper0577 : ℚ := (5862789/13107200000000)

def plusWeights0577 : Fin 11 → ℚ := ![(5862789/13107200000000), (5862789/1310720000000), (52765101/2621440000000), (17588367/327680000000), (123118569/1310720000000), (368011707/3276800000000), (120388329/1310720000000), (16200619/327680000000), (207346273/13107200000000), (14934697/6553600000000), 0]

def minusWeights0577 : Fin 11 → ℚ := ![(5862789/13107200000000), (5862789/1310720000000), (52765101/2621440000000), (17588367/327680000000), (123118569/1310720000000), (370699707/3276800000000), (125848809/1310720000000), (3795223/65536000000), (320304737/13107200000000), (43693193/6553600000000), (5862789/6553600000000)]

theorem checked0577 :
    (∀ i, 0 ≤ plusWeights0577 i) ∧
    (∀ i, 0 ≤ minusWeights0577 i) ∧
    (∀ i, plusCoefficients coefficients0577 upper0577 i = powerCoefficients10 plusWeights0577 i) ∧
    (∀ i, minusCoefficients coefficients0577 upper0577 i = powerCoefficients10 minusWeights0577 i) := by
  decide +kernel

theorem bound0577 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0577 g| ≤ (upper0577 : ℝ) :=
  abs_of_coefficients coefficients0577 upper0577 powerCoefficients10 plusWeights0577 minusWeights0577
    checked0577.1 checked0577.2.1 checked0577.2.2.1 checked0577.2.2.2
    (power_identity10 plusWeights0577) (power_identity10 minusWeights0577) g hg hmax

def envelope0577 : Envelope := ⟨coefficients0577, upper0577, bound0577⟩

def coefficients0578 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-17/512), (-17/1024), (-337/8192), (-143/4096), (-875/32768), (-565/65536)]

def upper0578 : ℚ := (46284573/131072000000000)

def plusWeights0578 : Fin 11 → ℚ := ![(46284573/131072000000000), (46284573/13107200000000), (416561157/26214400000000), (138853719/3276800000000), (971976033/13107200000000), (2905048099/32768000000000), (949998433/13107200000000), (127742639/3276800000000), (65315457/5242880000000), (23482911/13107200000000), 0]

def minusWeights0578 : Fin 11 → ℚ := ![(46284573/131072000000000), (46284573/13107200000000), (416561157/26214400000000), (138853719/3276800000000), (971976033/13107200000000), (2926808099/32768000000000), (993953633/13107200000000), (149964799/3276800000000), (506545029/26214400000000), (13817247/2621440000000), (46284573/65536000000000)]

theorem checked0578 :
    (∀ i, 0 ≤ plusWeights0578 i) ∧
    (∀ i, 0 ≤ minusWeights0578 i) ∧
    (∀ i, plusCoefficients coefficients0578 upper0578 i = powerCoefficients10 plusWeights0578 i) ∧
    (∀ i, minusCoefficients coefficients0578 upper0578 i = powerCoefficients10 minusWeights0578 i) := by
  decide +kernel

theorem bound0578 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0578 g| ≤ (upper0578 : ℝ) :=
  abs_of_coefficients coefficients0578 upper0578 powerCoefficients10 plusWeights0578 minusWeights0578
    checked0578.1 checked0578.2.1 checked0578.2.2.1 checked0578.2.2.2
    (power_identity10 plusWeights0578) (power_identity10 minusWeights0578) g hg hmax

def envelope0578 : Envelope := ⟨coefficients0578, upper0578, bound0578⟩

def coefficients0579 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (3/256), (-157/2048), (-189/2048), (-1943/32768), (-1171/65536)]

def upper0579 : ℚ := (202788831/655360000000000)

def plusWeights0579 : Fin 11 → ℚ := ![(202788831/655360000000000), (202788831/65536000000000), (1825099479/131072000000000), (608366493/16384000000000), (4258565451/65536000000000), (12724496353/163840000000000), (4156933451/65536000000000), (557808893/16384000000000), (1421580119/131072000000000), (20365757/13107200000000), 0]

def minusWeights0579 : Fin 11 → ℚ := ![(202788831/655360000000000), (202788831/65536000000000), (1825099479/131072000000000), (608366493/16384000000000), (4258565451/65536000000000), (12826896353/163840000000000), (4360197451/65536000000000), (658924093/16384000000000), (2228618839/131072000000000), (303748877/65536000000000), (202788831/327680000000000)]

theorem checked0579 :
    (∀ i, 0 ≤ plusWeights0579 i) ∧
    (∀ i, 0 ≤ minusWeights0579 i) ∧
    (∀ i, plusCoefficients coefficients0579 upper0579 i = powerCoefficients10 plusWeights0579 i) ∧
    (∀ i, minusCoefficients coefficients0579 upper0579 i = powerCoefficients10 minusWeights0579 i) := by
  decide +kernel

theorem bound0579 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0579 g| ≤ (upper0579 : ℝ) :=
  abs_of_coefficients coefficients0579 upper0579 powerCoefficients10 plusWeights0579 minusWeights0579
    checked0579.1 checked0579.2.1 checked0579.2.2.1 checked0579.2.2.2
    (power_identity10 plusWeights0579) (power_identity10 minusWeights0579) g hg hmax

def envelope0579 : Envelope := ⟨coefficients0579, upper0579, bound0579⟩

def coefficients0580 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (7/512), (143/8192), (2059/32768), (1723/65536), (5515/524288)]

def upper0580 : ℚ := (310826049/1048576000000000)

def plusWeights0580 : Fin 11 → ℚ := ![(310826049/1048576000000000), (310826049/104857600000000), (2797434441/209715200000000), (932478147/26214400000000), (6527347029/104857600000000), (19500121087/262144000000000), (6364940629/104857600000000), (852037507/26214400000000), (2160507657/209715200000000), (767020509/524288000000000), 0]

def minusWeights0580 : Fin 11 → ℚ := ![(310826049/1048576000000000), (310826049/104857600000000), (2797434441/209715200000000), (932478147/26214400000000), (6527347029/104857600000000), (19663961087/262144000000000), (6689753429/104857600000000), (1012918787/26214400000000), (137374449/8388608000000), (2341239981/524288000000000), (310826049/524288000000000)]

theorem checked0580 :
    (∀ i, 0 ≤ plusWeights0580 i) ∧
    (∀ i, 0 ≤ minusWeights0580 i) ∧
    (∀ i, plusCoefficients coefficients0580 upper0580 i = powerCoefficients10 plusWeights0580 i) ∧
    (∀ i, minusCoefficients coefficients0580 upper0580 i = powerCoefficients10 minusWeights0580 i) := by
  decide +kernel

theorem bound0580 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0580 g| ≤ (upper0580 : ℝ) :=
  abs_of_coefficients coefficients0580 upper0580 powerCoefficients10 plusWeights0580 minusWeights0580
    checked0580.1 checked0580.2.1 checked0580.2.2.1 checked0580.2.2.2
    (power_identity10 plusWeights0580) (power_identity10 minusWeights0580) g hg hmax

def envelope0580 : Envelope := ⟨coefficients0580, upper0580, bound0580⟩

def coefficients0581 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/32), (7/512), (143/8192), (2599/32768), (2503/65536), (12475/524288)]

def upper0581 : ℚ := (310639377/1048576000000000)

def plusWeights0581 : Fin 11 → ℚ := ![(310639377/1048576000000000), (310639377/104857600000000), (2795754393/209715200000000), (931918131/26214400000000), (6523426917/104857600000000), (19488360751/262144000000000), (6361020517/104857600000000), (851477491/26214400000000), (2158862169/209715200000000), (766266189/524288000000000), 0]

def minusWeights0581 : Fin 11 → ℚ := ![(310639377/1048576000000000), (310639377/104857600000000), (2795754393/209715200000000), (931918131/26214400000000), (6523426917/104857600000000), (19652200751/262144000000000), (6685833317/104857600000000), (1012358771/26214400000000), (3432646617/209715200000000), (2340127581/524288000000000), (310639377/524288000000000)]

theorem checked0581 :
    (∀ i, 0 ≤ plusWeights0581 i) ∧
    (∀ i, 0 ≤ minusWeights0581 i) ∧
    (∀ i, plusCoefficients coefficients0581 upper0581 i = powerCoefficients10 plusWeights0581 i) ∧
    (∀ i, minusCoefficients coefficients0581 upper0581 i = powerCoefficients10 minusWeights0581 i) := by
  decide +kernel

theorem bound0581 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0581 g| ≤ (upper0581 : ℝ) :=
  abs_of_coefficients coefficients0581 upper0581 powerCoefficients10 plusWeights0581 minusWeights0581
    checked0581.1 checked0581.2.1 checked0581.2.2.1 checked0581.2.2.2
    (power_identity10 plusWeights0581) (power_identity10 minusWeights0581) g hg hmax

def envelope0581 : Envelope := ⟨coefficients0581, upper0581, bound0581⟩

def coefficients0582 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (3/512), (117/8192), (1149/32768), (993/65536), (3615/524288)]

def upper0582 : ℚ := (299174109/1048576000000000)

def plusWeights0582 : Fin 11 → ℚ := ![(299174109/1048576000000000), (299174109/104857600000000), (2692566981/209715200000000), (897522327/26214400000000), (6282656289/104857600000000), (18771168867/262144000000000), (6129670689/104857600000000), (821374167/26214400000000), (2086511877/209715200000000), (742780569/524288000000000), 0]

def minusWeights0582 : Fin 11 → ℚ := ![(299174109/1048576000000000), (299174109/104857600000000), (2692566981/209715200000000), (897522327/26214400000000), (6282656289/104857600000000), (18924768867/262144000000000), (6435641889/104857600000000), (973670487/26214400000000), (659724417/41943040000000), (2248960521/524288000000000), (299174109/524288000000000)]

theorem checked0582 :
    (∀ i, 0 ≤ plusWeights0582 i) ∧
    (∀ i, 0 ≤ minusWeights0582 i) ∧
    (∀ i, plusCoefficients coefficients0582 upper0582 i = powerCoefficients10 plusWeights0582 i) ∧
    (∀ i, minusCoefficients coefficients0582 upper0582 i = powerCoefficients10 minusWeights0582 i) := by
  decide +kernel

theorem bound0582 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0582 g| ≤ (upper0582 : ℝ) :=
  abs_of_coefficients coefficients0582 upper0582 powerCoefficients10 plusWeights0582 minusWeights0582
    checked0582.1 checked0582.2.1 checked0582.2.2.1 checked0582.2.2.2
    (power_identity10 plusWeights0582) (power_identity10 minusWeights0582) g hg hmax

def envelope0582 : Envelope := ⟨coefficients0582, upper0582, bound0582⟩

def coefficients0583 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (29/2048), (209/8192), (337/8192), (71/4096), (3605/524288)]

def upper0583 : ℚ := (289226543/1048576000000000)

def plusWeights0583 : Fin 11 → ℚ := ![(289226543/1048576000000000), (289226543/104857600000000), (2603038887/209715200000000), (867679629/26214400000000), (6073757403/104857600000000), (18144472209/262144000000000), (5921642203/104857600000000), (792431309/26214400000000), (2008147879/209715200000000), (712281963/524288000000000), 0]

def minusWeights0583 : Fin 11 → ℚ := ![(289226543/1048576000000000), (289226543/104857600000000), (2603038887/209715200000000), (867679629/26214400000000), (6073757403/104857600000000), (18298072209/262144000000000), (6225872603/104857600000000), (942927949/26214400000000), (639585979/41943040000000), (2179983467/524288000000000), (289226543/524288000000000)]

theorem checked0583 :
    (∀ i, 0 ≤ plusWeights0583 i) ∧
    (∀ i, 0 ≤ minusWeights0583 i) ∧
    (∀ i, plusCoefficients coefficients0583 upper0583 i = powerCoefficients10 plusWeights0583 i) ∧
    (∀ i, minusCoefficients coefficients0583 upper0583 i = powerCoefficients10 minusWeights0583 i) := by
  decide +kernel

theorem bound0583 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0583 g| ≤ (upper0583 : ℝ) :=
  abs_of_coefficients coefficients0583 upper0583 powerCoefficients10 plusWeights0583 minusWeights0583
    checked0583.1 checked0583.2.1 checked0583.2.2.1 checked0583.2.2.2
    (power_identity10 plusWeights0583) (power_identity10 minusWeights0583) g hg hmax

def envelope0583 : Envelope := ⟨coefficients0583, upper0583, bound0583⟩

def coefficients0584 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (17/1024), (189/8192), (93/2048), (3/128), (785/65536)]

def upper0584 : ℚ := (35858851/131072000000000)

def plusWeights0584 : Fin 11 → ℚ := ![(35858851/131072000000000), (35858851/13107200000000), (322729659/26214400000000), (107576553/3276800000000), (753035871/13107200000000), (2249507613/32768000000000), (734053471/13107200000000), (98201713/3276800000000), (248734203/26214400000000), (88160911/65536000000000), 0]

def minusWeights0584 : Fin 11 → ℚ := ![(35858851/131072000000000), (35858851/13107200000000), (322729659/26214400000000), (107576553/3276800000000), (753035871/13107200000000), (2268707613/32768000000000), (772018271/13107200000000), (116951393/3276800000000), (79345023/5242880000000), (270427599/65536000000000), (35858851/65536000000000)]

theorem checked0584 :
    (∀ i, 0 ≤ plusWeights0584 i) ∧
    (∀ i, 0 ≤ minusWeights0584 i) ∧
    (∀ i, plusCoefficients coefficients0584 upper0584 i = powerCoefficients10 plusWeights0584 i) ∧
    (∀ i, minusCoefficients coefficients0584 upper0584 i = powerCoefficients10 minusWeights0584 i) := by
  decide +kernel

theorem bound0584 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0584 g| ≤ (upper0584 : ℝ) :=
  abs_of_coefficients coefficients0584 upper0584 powerCoefficients10 plusWeights0584 minusWeights0584
    checked0584.1 checked0584.2.1 checked0584.2.2.1 checked0584.2.2.2
    (power_identity10 plusWeights0584) (power_identity10 minusWeights0584) g hg hmax

def envelope0584 : Envelope := ⟨coefficients0584, upper0584, bound0584⟩

def coefficients0585 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (39/2048), (249/8192), (93/2048), (309/16384), (3855/524288)]

def upper0585 : ℚ := (283548093/1048576000000000)

def plusWeights0585 : Fin 11 → ℚ := ![(283548093/1048576000000000), (283548093/104857600000000), (2551932837/209715200000000), (850644279/26214400000000), (5954509953/104857600000000), (17786729859/262144000000000), (5802906753/104857600000000), (775920759/26214400000000), (1963501989/209715200000000), (694943313/524288000000000), 0]

def minusWeights0585 : Fin 11 → ℚ := ![(283548093/1048576000000000), (283548093/104857600000000), (2551932837/209715200000000), (850644279/26214400000000), (5954509953/104857600000000), (17940329859/262144000000000), (6106113153/104857600000000), (925367799/26214400000000), (628072737/41943040000000), (2140537617/524288000000000), (283548093/524288000000000)]

theorem checked0585 :
    (∀ i, 0 ≤ plusWeights0585 i) ∧
    (∀ i, 0 ≤ minusWeights0585 i) ∧
    (∀ i, plusCoefficients coefficients0585 upper0585 i = powerCoefficients10 plusWeights0585 i) ∧
    (∀ i, minusCoefficients coefficients0585 upper0585 i = powerCoefficients10 minusWeights0585 i) := by
  decide +kernel

theorem bound0585 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0585 g| ≤ (upper0585 : ℝ) :=
  abs_of_coefficients coefficients0585 upper0585 powerCoefficients10 plusWeights0585 minusWeights0585
    checked0585.1 checked0585.2.1 checked0585.2.2.1 checked0585.2.2.2
    (power_identity10 plusWeights0585) (power_identity10 minusWeights0585) g hg hmax

def envelope0585 : Envelope := ⟨coefficients0585, upper0585, bound0585⟩

def coefficients0586 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-15/512), (27/1024), (189/8192), (477/8192), (609/16384), (7065/262144)]

def upper0586 : ℚ := (138240219/524288000000000)

def plusWeights0586 : Fin 11 → ℚ := ![(138240219/524288000000000), (138240219/52428800000000), (1244161971/104857600000000), (414720657/13107200000000), (2903044599/52428800000000), (8670733797/131072000000000), (2827626999/52428800000000), (377733297/13107200000000), (954337587/104857600000000), (336978519/262144000000000), 0]

def minusWeights0586 : Fin 11 → ℚ := ![(138240219/524288000000000), (138240219/52428800000000), (1244161971/104857600000000), (414720657/13107200000000), (2903044599/52428800000000), (8747533797/131072000000000), (2978462199/52428800000000), (451708017/13107200000000), (306797271/20971520000000), (1045423671/262144000000000), (138240219/262144000000000)]

theorem checked0586 :
    (∀ i, 0 ≤ plusWeights0586 i) ∧
    (∀ i, 0 ≤ minusWeights0586 i) ∧
    (∀ i, plusCoefficients coefficients0586 upper0586 i = powerCoefficients10 plusWeights0586 i) ∧
    (∀ i, minusCoefficients coefficients0586 upper0586 i = powerCoefficients10 minusWeights0586 i) := by
  decide +kernel

theorem bound0586 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0586 g| ≤ (upper0586 : ℝ) :=
  abs_of_coefficients coefficients0586 upper0586 powerCoefficients10 plusWeights0586 minusWeights0586
    checked0586.1 checked0586.2.1 checked0586.2.2.1 checked0586.2.2.2
    (power_identity10 plusWeights0586) (power_identity10 minusWeights0586) g hg hmax

def envelope0586 : Envelope := ⟨coefficients0586, upper0586, bound0586⟩

def coefficients0587 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-29/512), (-893/8192), (-135/2048), (-5623/65536), (-4431/131072)]

def upper0587 : ℚ := (396708891/1310720000000000)

def plusWeights0587 : Fin 11 → ℚ := ![(396708891/1310720000000000), (396708891/131072000000000), (3570380019/262144000000000), (1190126673/32768000000000), (8330886711/131072000000000), (24915860133/327680000000000), (8169862711/131072000000000), (1105545473/32768000000000), (2858146419/262144000000000), (41788489/26214400000000), 0]

def minusWeights0587 : Fin 11 → ℚ := ![(396708891/1310720000000000), (396708891/131072000000000), (3570380019/262144000000000), (1190126673/32768000000000), (8330886711/131072000000000), (25069460133/327680000000000), (8491910711/131072000000000), (1274707873/32768000000000), (4282613619/262144000000000), (584475337/131072000000000), (396708891/655360000000000)]

theorem checked0587 :
    (∀ i, 0 ≤ plusWeights0587 i) ∧
    (∀ i, 0 ≤ minusWeights0587 i) ∧
    (∀ i, plusCoefficients coefficients0587 upper0587 i = powerCoefficients10 plusWeights0587 i) ∧
    (∀ i, minusCoefficients coefficients0587 upper0587 i = powerCoefficients10 minusWeights0587 i) := by
  decide +kernel

theorem bound0587 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0587 g| ≤ (upper0587 : ℝ) :=
  abs_of_coefficients coefficients0587 upper0587 powerCoefficients10 plusWeights0587 minusWeights0587
    checked0587.1 checked0587.2.1 checked0587.2.2.1 checked0587.2.2.2
    (power_identity10 plusWeights0587) (power_identity10 minusWeights0587) g hg hmax

def envelope0587 : Envelope := ⟨coefficients0587, upper0587, bound0587⟩

def coefficients0588 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-29/512), (-545/8192), (-21/1024), (-2635/65536), (-2235/131072)]

def upper0588 : ℚ := (78096747/262144000000000)

def plusWeights0588 : Fin 11 → ℚ := ![(78096747/262144000000000), (78096747/26214400000000), (702870723/52428800000000), (234290241/6553600000000), (1640031687/26214400000000), (4904735061/65536000000000), (1607826887/26214400000000), (217401841/6553600000000), (561115971/52428800000000), (40902541/26214400000000), 0]

def minusWeights0588 : Fin 11 → ℚ := ![(78096747/262144000000000), (78096747/26214400000000), (702870723/52428800000000), (234290241/6553600000000), (1640031687/26214400000000), (4935455061/65536000000000), (1672236487/26214400000000), (251178641/6553600000000), (33785019/2097152000000), (115290953/26214400000000), (78096747/131072000000000)]

theorem checked0588 :
    (∀ i, 0 ≤ plusWeights0588 i) ∧
    (∀ i, 0 ≤ minusWeights0588 i) ∧
    (∀ i, plusCoefficients coefficients0588 upper0588 i = powerCoefficients10 plusWeights0588 i) ∧
    (∀ i, minusCoefficients coefficients0588 upper0588 i = powerCoefficients10 minusWeights0588 i) := by
  decide +kernel

theorem bound0588 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0588 g| ≤ (upper0588 : ℝ) :=
  abs_of_coefficients coefficients0588 upper0588 powerCoefficients10 plusWeights0588 minusWeights0588
    checked0588.1 checked0588.2.1 checked0588.2.2.1 checked0588.2.2.2
    (power_identity10 plusWeights0588) (power_identity10 minusWeights0588) g hg hmax

def envelope0588 : Envelope := ⟨coefficients0588, upper0588, bound0588⟩

def coefficients0589 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-43/1024), (-751/8192), (-241/4096), (-1369/16384), (-17/512)]

def upper0589 : ℚ := (23446317/81920000000000)

def plusWeights0589 : Fin 11 → ℚ := ![(23446317/81920000000000), (23446317/8192000000000), (211016853/16384000000000), (70338951/2048000000000), (492372657/8192000000000), (1472317971/20480000000000), (482428657/8192000000000), (4073511/128000000000), (168028613/16384000000000), (4893877/3276800000000), 0]

def minusWeights0589 : Fin 11 → ℚ := ![(23446317/81920000000000), (23446317/8192000000000), (211016853/16384000000000), (70338951/2048000000000), (492372657/8192000000000), (1481917971/20480000000000), (502316657/8192000000000), (37750863/1024000000000), (254005093/16384000000000), (69315883/16384000000000), (23446317/40960000000000)]

theorem checked0589 :
    (∀ i, 0 ≤ plusWeights0589 i) ∧
    (∀ i, 0 ≤ minusWeights0589 i) ∧
    (∀ i, plusCoefficients coefficients0589 upper0589 i = powerCoefficients10 plusWeights0589 i) ∧
    (∀ i, minusCoefficients coefficients0589 upper0589 i = powerCoefficients10 minusWeights0589 i) := by
  decide +kernel

theorem bound0589 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0589 g| ≤ (upper0589 : ℝ) :=
  abs_of_coefficients coefficients0589 upper0589 powerCoefficients10 plusWeights0589 minusWeights0589
    checked0589.1 checked0589.2.1 checked0589.2.2.1 checked0589.2.2.2
    (power_identity10 plusWeights0589) (power_identity10 minusWeights0589) g hg hmax

def envelope0589 : Envelope := ⟨coefficients0589, upper0589, bound0589⟩

def coefficients0590 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-43/1024), (-661/8192), (-271/4096), (-999/16384), (-43/2048)]

def upper0590 : ℚ := (23360367/81920000000000)

def plusWeights0590 : Fin 11 → ℚ := ![(23360367/81920000000000), (23360367/8192000000000), (210243303/16384000000000), (70081101/2048000000000), (490567707/8192000000000), (1466903121/20480000000000), (480623707/8192000000000), (63399/2000000000), (167307863/16384000000000), (4869891/3276800000000), 0]

def minusWeights0590 : Fin 11 → ℚ := ![(23360367/81920000000000), (23360367/8192000000000), (210243303/16384000000000), (70081101/2048000000000), (490567707/8192000000000), (1476503121/20480000000000), (500511707/8192000000000), (37620813/1024000000000), (253178743/16384000000000), (69092013/16384000000000), (23360367/40960000000000)]

theorem checked0590 :
    (∀ i, 0 ≤ plusWeights0590 i) ∧
    (∀ i, 0 ≤ minusWeights0590 i) ∧
    (∀ i, plusCoefficients coefficients0590 upper0590 i = powerCoefficients10 plusWeights0590 i) ∧
    (∀ i, minusCoefficients coefficients0590 upper0590 i = powerCoefficients10 minusWeights0590 i) := by
  decide +kernel

theorem bound0590 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0590 g| ≤ (upper0590 : ℝ) :=
  abs_of_coefficients coefficients0590 upper0590 powerCoefficients10 plusWeights0590 minusWeights0590
    checked0590.1 checked0590.2.1 checked0590.2.2.1 checked0590.2.2.2
    (power_identity10 plusWeights0590) (power_identity10 minusWeights0590) g hg hmax

def envelope0590 : Envelope := ⟨coefficients0590, upper0590, bound0590⟩

def coefficients0591 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-43/1024), (-415/8192), (-49/4096), (-145/4096), (-515/32768)]

def upper0591 : ℚ := (18454263/65536000000000)

def plusWeights0591 : Fin 11 → ℚ := ![(18454263/65536000000000), (18454263/6553600000000), (166088367/13107200000000), (55362789/1638400000000), (387539523/6553600000000), (1158778569/16384000000000), (379584323/6553600000000), (51239289/1638400000000), (131865199/13107200000000), (9572063/6553600000000), 0]

def minusWeights0591 : Fin 11 → ℚ := ![(18454263/65536000000000), (18454263/6553600000000), (166088367/13107200000000), (55362789/1638400000000), (387539523/6553600000000), (1166458569/16384000000000), (395494723/6553600000000), (59486289/1638400000000), (40062307/2621440000000), (27336463/6553600000000), (18454263/32768000000000)]

theorem checked0591 :
    (∀ i, 0 ≤ plusWeights0591 i) ∧
    (∀ i, 0 ≤ minusWeights0591 i) ∧
    (∀ i, plusCoefficients coefficients0591 upper0591 i = powerCoefficients10 plusWeights0591 i) ∧
    (∀ i, minusCoefficients coefficients0591 upper0591 i = powerCoefficients10 minusWeights0591 i) := by
  decide +kernel

theorem bound0591 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0591 g| ≤ (upper0591 : ℝ) :=
  abs_of_coefficients coefficients0591 upper0591 powerCoefficients10 plusWeights0591 minusWeights0591
    checked0591.1 checked0591.2.1 checked0591.2.2.1 checked0591.2.2.2
    (power_identity10 plusWeights0591) (power_identity10 minusWeights0591) g hg hmax

def envelope0591 : Envelope := ⟨coefficients0591, upper0591, bound0591⟩

def coefficients0592 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/128), (-19/512), (-531/8192), (-49/1024), (-3931/65536), (-3067/131072)]

def upper0592 : ℚ := (365044887/1310720000000000)

def plusWeights0592 : Fin 11 → ℚ := ![(365044887/1310720000000000), (365044887/131072000000000), (3285403983/262144000000000), (1095134661/32768000000000), (7665942627/131072000000000), (22921027881/327680000000000), (7507478627/131072000000000), (1013258261/32768000000000), (2607412943/262144000000000), (37861357/26214400000000), 0]

def minusWeights0592 : Fin 11 → ℚ := ![(365044887/1310720000000000), (365044887/131072000000000), (3285403983/262144000000000), (1095134661/32768000000000), (7665942627/131072000000000), (23074627881/327680000000000), (7824406627/131072000000000), (1177011061/32768000000000), (3963395023/262144000000000), (540782989/131072000000000), (365044887/655360000000000)]

theorem checked0592 :
    (∀ i, 0 ≤ plusWeights0592 i) ∧
    (∀ i, 0 ≤ minusWeights0592 i) ∧
    (∀ i, plusCoefficients coefficients0592 upper0592 i = powerCoefficients10 plusWeights0592 i) ∧
    (∀ i, minusCoefficients coefficients0592 upper0592 i = powerCoefficients10 minusWeights0592 i) := by
  decide +kernel

theorem bound0592 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0592 g| ≤ (upper0592 : ℝ) :=
  abs_of_coefficients coefficients0592 upper0592 powerCoefficients10 plusWeights0592 minusWeights0592
    checked0592.1 checked0592.2.1 checked0592.2.2.1 checked0592.2.2.2
    (power_identity10 plusWeights0592) (power_identity10 minusWeights0592) g hg hmax

def envelope0592 : Envelope := ⟨coefficients0592, upper0592, bound0592⟩

def coefficients0593 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/256), (-5/512), (-65/4096), (-5/512), (-45/8192), (-25/16384)]

def upper0593 : ℚ := (1355077/6553600000000)

def plusWeights0593 : Fin 11 → ℚ := ![(1355077/6553600000000), (1355077/655360000000), (12195693/1310720000000), (4065231/163840000000), (28456617/655360000000), (85049851/1638400000000), (27810217/655360000000), (3738571/163840000000), (382101/52428800000), (3431127/3276800000000), 0]

def minusWeights0593 : Fin 11 → ℚ := ![(1355077/6553600000000), (1355077/655360000000), (12195693/1310720000000), (4065231/163840000000), (28456617/655360000000), (85689851/1638400000000), (29103017/655360000000), (4391891/163840000000), (14838861/1310720000000), (10119643/3276800000000), (1355077/3276800000000)]

theorem checked0593 :
    (∀ i, 0 ≤ plusWeights0593 i) ∧
    (∀ i, 0 ≤ minusWeights0593 i) ∧
    (∀ i, plusCoefficients coefficients0593 upper0593 i = powerCoefficients10 plusWeights0593 i) ∧
    (∀ i, minusCoefficients coefficients0593 upper0593 i = powerCoefficients10 minusWeights0593 i) := by
  decide +kernel

theorem bound0593 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0593 g| ≤ (upper0593 : ℝ) :=
  abs_of_coefficients coefficients0593 upper0593 powerCoefficients10 plusWeights0593 minusWeights0593
    checked0593.1 checked0593.2.1 checked0593.2.2.1 checked0593.2.2.2
    (power_identity10 plusWeights0593) (power_identity10 minusWeights0593) g hg hmax

def envelope0593 : Envelope := ⟨coefficients0593, upper0593, bound0593⟩

def coefficients0594 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-5/256), (-5/512), (-35/4096), (-5/2048), (-45/32768), (-25/65536)]

def upper0594 : ℚ := (5399077/26214400000000)

def plusWeights0594 : Fin 11 → ℚ := ![(5399077/26214400000000), (5399077/2621440000000), (48591693/5242880000000), (16197231/655360000000), (113380617/2621440000000), (338861851/6553600000000), (110795017/2621440000000), (14891071/655360000000), (1521237/209715200000), (13649127/13107200000000), 0]

def minusWeights0594 : Fin 11 → ℚ := ![(5399077/26214400000000), (5399077/2621440000000), (48591693/5242880000000), (16197231/655360000000), (113380617/2621440000000), (341421851/6553600000000), (115966217/2621440000000), (17503391/655360000000), (59152461/5242880000000), (40341643/13107200000000), (5399077/13107200000000)]

theorem checked0594 :
    (∀ i, 0 ≤ plusWeights0594 i) ∧
    (∀ i, 0 ≤ minusWeights0594 i) ∧
    (∀ i, plusCoefficients coefficients0594 upper0594 i = powerCoefficients10 plusWeights0594 i) ∧
    (∀ i, minusCoefficients coefficients0594 upper0594 i = powerCoefficients10 minusWeights0594 i) := by
  decide +kernel

theorem bound0594 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0594 g| ≤ (upper0594 : ℝ) :=
  abs_of_coefficients coefficients0594 upper0594 powerCoefficients10 plusWeights0594 minusWeights0594
    checked0594.1 checked0594.2.1 checked0594.2.2.1 checked0594.2.2.2
    (power_identity10 plusWeights0594) (power_identity10 minusWeights0594) g hg hmax

def envelope0594 : Envelope := ⟨coefficients0594, upper0594, bound0594⟩

def coefficients0595 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-9/512), (-9/1024), (-219/8192), (-121/4096), (-1215/65536), (-635/131072)]

def upper0595 : ℚ := (49167227/262144000000000)

def plusWeights0595 : Fin 11 → ℚ := ![(49167227/262144000000000), (49167227/26214400000000), (442505043/52428800000000), (147501681/6553600000000), (1032511767/26214400000000), (3086015301/65536000000000), (1009241367/26214400000000), (135733761/6553600000000), (13885771/2097152000000), (24979413/26214400000000), 0]

def minusWeights0595 : Fin 11 → ℚ := ![(49167227/262144000000000), (49167227/26214400000000), (442505043/52428800000000), (147501681/6553600000000), (1032511767/26214400000000), (3109055301/65536000000000), (1055782167/26214400000000), (159269601/6553600000000), (537865811/52428800000000), (73355041/26214400000000), (49167227/131072000000000)]

theorem checked0595 :
    (∀ i, 0 ≤ plusWeights0595 i) ∧
    (∀ i, 0 ≤ minusWeights0595 i) ∧
    (∀ i, plusCoefficients coefficients0595 upper0595 i = powerCoefficients10 plusWeights0595 i) ∧
    (∀ i, minusCoefficients coefficients0595 upper0595 i = powerCoefficients10 minusWeights0595 i) := by
  decide +kernel

theorem bound0595 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0595 g| ≤ (upper0595 : ℝ) :=
  abs_of_coefficients coefficients0595 upper0595 powerCoefficients10 plusWeights0595 minusWeights0595
    checked0595.1 checked0595.2.1 checked0595.2.2.1 checked0595.2.2.2
    (power_identity10 plusWeights0595) (power_identity10 minusWeights0595) g hg hmax

def envelope0595 : Envelope := ⟨coefficients0595, upper0595, bound0595⟩

def coefficients0596 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (1/1024), (-269/4096), (-307/4096), (-3757/65536), (-2449/131072)]

def upper0596 : ℚ := (213187989/1310720000000000)

def plusWeights0596 : Fin 11 → ℚ := ![(213187989/1310720000000000), (213187989/131072000000000), (1918691901/262144000000000), (639563967/32768000000000), (4476947769/131072000000000), (13379643307/327680000000000), (4374675769/131072000000000), (588276767/32768000000000), (1505266621/262144000000000), (21702719/26214400000000), 0]

def minusWeights0596 : Fin 11 → ℚ := ![(213187989/1310720000000000), (213187989/131072000000000), (1918691901/262144000000000), (639563967/32768000000000), (4476947769/131072000000000), (13482043307/327680000000000), (4579219769/131072000000000), (690851167/32768000000000), (2332117181/262144000000000), (317862383/131072000000000), (213187989/655360000000000)]

theorem checked0596 :
    (∀ i, 0 ≤ plusWeights0596 i) ∧
    (∀ i, 0 ≤ minusWeights0596 i) ∧
    (∀ i, plusCoefficients coefficients0596 upper0596 i = powerCoefficients10 plusWeights0596 i) ∧
    (∀ i, minusCoefficients coefficients0596 upper0596 i = powerCoefficients10 minusWeights0596 i) := by
  decide +kernel

theorem bound0596 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0596 g| ≤ (upper0596 : ℝ) :=
  abs_of_coefficients coefficients0596 upper0596 powerCoefficients10 plusWeights0596 minusWeights0596
    checked0596.1 checked0596.2.1 checked0596.2.2.1 checked0596.2.2.2
    (power_identity10 plusWeights0596) (power_identity10 minusWeights0596) g hg hmax

def envelope0596 : Envelope := ⟨coefficients0596, upper0596, bound0596⟩

def coefficients0597 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (5/2048), (65/8192), (577/16384), (509/32768), (3865/524288)]

def upper0597 : ℚ := (160061659/1048576000000000)

def plusWeights0597 : Fin 11 → ℚ := ![(160061659/1048576000000000), (160061659/104857600000000), (1440554931/209715200000000), (480184977/26214400000000), (3361294839/104857600000000), (10042924517/262144000000000), (3279630839/104857600000000), (439501777/26214400000000), (1116519987/209715200000000), (397453719/524288000000000), 0]

def minusWeights0597 : Fin 11 → ℚ := ![(160061659/1048576000000000), (160061659/104857600000000), (1440554931/209715200000000), (480184977/26214400000000), (3361294839/104857600000000), (10124844517/262144000000000), (3442958839/104857600000000), (520868177/26214400000000), (14116719/1677721600000), (1203162871/524288000000000), (160061659/524288000000000)]

theorem checked0597 :
    (∀ i, 0 ≤ plusWeights0597 i) ∧
    (∀ i, 0 ≤ minusWeights0597 i) ∧
    (∀ i, plusCoefficients coefficients0597 upper0597 i = powerCoefficients10 plusWeights0597 i) ∧
    (∀ i, minusCoefficients coefficients0597 upper0597 i = powerCoefficients10 minusWeights0597 i) := by
  decide +kernel

theorem bound0597 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0597 g| ≤ (upper0597 : ℝ) :=
  abs_of_coefficients coefficients0597 upper0597 powerCoefficients10 plusWeights0597 minusWeights0597
    checked0597.1 checked0597.2.1 checked0597.2.2.1 checked0597.2.2.2
    (power_identity10 plusWeights0597) (power_identity10 minusWeights0597) g hg hmax

def envelope0597 : Envelope := ⟨coefficients0597, upper0597, bound0597⟩

def coefficients0598 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (41/2048), (91/8192), (29/512), (199/8192), (5435/524288)]

def upper0598 : ℚ := (141062721/1048576000000000)

def plusWeights0598 : Fin 11 → ℚ := ![(141062721/1048576000000000), (141062721/104857600000000), (1269564489/209715200000000), (423188163/26214400000000), (2962317141/104857600000000), (8845991423/262144000000000), (2882496341/104857600000000), (384356483/26214400000000), (967892553/209715200000000), (340051461/524288000000000), 0]

def minusWeights0598 : Fin 11 → ℚ := ![(141062721/1048576000000000), (141062721/104857600000000), (1269564489/209715200000000), (423188163/26214400000000), (2962317141/104857600000000), (8927911423/262144000000000), (3042137941/104857600000000), (462019843/26214400000000), (62849457/8388608000000), (1070575749/524288000000000), (141062721/524288000000000)]

theorem checked0598 :
    (∀ i, 0 ≤ plusWeights0598 i) ∧
    (∀ i, 0 ≤ minusWeights0598 i) ∧
    (∀ i, plusCoefficients coefficients0598 upper0598 i = powerCoefficients10 plusWeights0598 i) ∧
    (∀ i, minusCoefficients coefficients0598 upper0598 i = powerCoefficients10 minusWeights0598 i) := by
  decide +kernel

theorem bound0598 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0598 g| ≤ (upper0598 : ℝ) :=
  abs_of_coefficients coefficients0598 upper0598 powerCoefficients10 plusWeights0598 minusWeights0598
    checked0598.1 checked0598.2.1 checked0598.2.2.1 checked0598.2.2.2
    (power_identity10 plusWeights0598) (power_identity10 minusWeights0598) g hg hmax

def envelope0598 : Envelope := ⟨coefficients0598, upper0598, bound0598⟩

def coefficients0599 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (41/2048), (91/8192), (3071/32768), (3347/65536), (25595/524288)]

def upper0599 : ℚ := (140641809/1048576000000000)

def plusWeights0599 : Fin 11 → ℚ := ![(140641809/1048576000000000), (140641809/104857600000000), (1265776281/209715200000000), (421925427/26214400000000), (2953477989/104857600000000), (8819473967/262144000000000), (2873657189/104857600000000), (383093747/26214400000000), (192836421/41943040000000), (338349741/524288000000000), 0]

def minusWeights0599 : Fin 11 → ℚ := ![(140641809/1048576000000000), (140641809/104857600000000), (1265776281/209715200000000), (421925427/26214400000000), (2953477989/104857600000000), (8901393967/262144000000000), (3033298789/104857600000000), (460757107/26214400000000), (1567370457/209715200000000), (1068068349/524288000000000), (140641809/524288000000000)]

theorem checked0599 :
    (∀ i, 0 ≤ plusWeights0599 i) ∧
    (∀ i, 0 ≤ minusWeights0599 i) ∧
    (∀ i, plusCoefficients coefficients0599 upper0599 i = powerCoefficients10 plusWeights0599 i) ∧
    (∀ i, minusCoefficients coefficients0599 upper0599 i = powerCoefficients10 minusWeights0599 i) := by
  decide +kernel

theorem bound0599 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0599 g| ≤ (upper0599 : ℝ) :=
  abs_of_coefficients coefficients0599 upper0599 powerCoefficients10 plusWeights0599 minusWeights0599
    checked0599.1 checked0599.2.1 checked0599.2.2.1 checked0599.2.2.2
    (power_identity10 plusWeights0599) (power_identity10 minusWeights0599) g hg hmax

def envelope0599 : Envelope := ⟨coefficients0599, upper0599, bound0599⟩

def coefficients0600 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (21/1024), (-305/4096), (-391/4096), (-5189/65536), (-3513/131072)]

def upper0600 : ℚ := (189038493/1310720000000000)

def plusWeights0600 : Fin 11 → ℚ := ![(189038493/1310720000000000), (189038493/131072000000000), (1701346437/262144000000000), (567115479/32768000000000), (3969808353/131072000000000), (11858225059/327680000000000), (3870096353/131072000000000), (518359479/32768000000000), (1317896197/262144000000000), (150723/209715200000), 0]

def minusWeights0600 : Fin 11 → ℚ := ![(189038493/1310720000000000), (189038493/131072000000000), (1701346437/262144000000000), (567115479/32768000000000), (3969808353/131072000000000), (11960625059/327680000000000), (4069520353/131072000000000), (615871479/32768000000000), (2084796677/262144000000000), (283875111/131072000000000), (189038493/655360000000000)]

theorem checked0600 :
    (∀ i, 0 ≤ plusWeights0600 i) ∧
    (∀ i, 0 ≤ minusWeights0600 i) ∧
    (∀ i, plusCoefficients coefficients0600 upper0600 i = powerCoefficients10 plusWeights0600 i) ∧
    (∀ i, minusCoefficients coefficients0600 upper0600 i = powerCoefficients10 minusWeights0600 i) := by
  decide +kernel

theorem bound0600 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0600 g| ≤ (upper0600 : ℝ) :=
  abs_of_coefficients coefficients0600 upper0600 powerCoefficients10 plusWeights0600 minusWeights0600
    checked0600.1 checked0600.2.1 checked0600.2.2.1 checked0600.2.2.2
    (power_identity10 plusWeights0600) (power_identity10 minusWeights0600) g hg hmax

def envelope0600 : Envelope := ⟨coefficients0600, upper0600, bound0600⟩

def coefficients0601 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (21/1024), (-143/4096), (-193/4096), (-1565/65536), (-825/131072)]

def upper0601 : ℚ := (7325829/52428800000000)

def plusWeights0601 : Fin 11 → ℚ := ![(7325829/52428800000000), (7325829/5242880000000), (65932461/10485760000000), (21977487/1310720000000), (153842409/5242880000000), (459479227/13107200000000), (149853929/5242880000000), (20032431/1310720000000), (253619681/52428800000000), (3599931/5242880000000), 0]

def minusWeights0601 : Fin 11 → ℚ := ![(7325829/52428800000000), (7325829/5242880000000), (65932461/10485760000000), (21977487/1310720000000), (153842409/5242880000000), (463575227/13107200000000), (157830889/5242880000000), (23922543/1310720000000), (405704929/52428800000000), (11051727/5242880000000), (7325829/26214400000000)]

theorem checked0601 :
    (∀ i, 0 ≤ plusWeights0601 i) ∧
    (∀ i, 0 ≤ minusWeights0601 i) ∧
    (∀ i, plusCoefficients coefficients0601 upper0601 i = powerCoefficients10 plusWeights0601 i) ∧
    (∀ i, minusCoefficients coefficients0601 upper0601 i = powerCoefficients10 minusWeights0601 i) := by
  decide +kernel

theorem bound0601 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0601 g| ≤ (upper0601 : ℝ) :=
  abs_of_coefficients coefficients0601 upper0601 powerCoefficients10 plusWeights0601 minusWeights0601
    checked0601.1 checked0601.2.1 checked0601.2.2.1 checked0601.2.2.2
    (power_identity10 plusWeights0601) (power_identity10 minusWeights0601) g hg hmax

def envelope0601 : Envelope := ⟨coefficients0601, upper0601, bound0601⟩

def coefficients0602 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-1/64), (17/512), (-1/4096), (1585/16384), (1405/32768), (5275/262144)]

def upper0602 : ℚ := (12798813/104857600000000)

def plusWeights0602 : Fin 11 → ℚ := ![(12798813/104857600000000), (12798813/10485760000000), (115189317/20971520000000), (38396439/2621440000000), (268775073/10485760000000), (802229219/26214400000000), (260931233/10485760000000), (6929707/524288000000), (86617989/20971520000000), (30097113/52428800000000), 0]

def minusWeights0602 : Fin 11 → ℚ := ![(12798813/104857600000000), (12798813/10485760000000), (115189317/20971520000000), (38396439/2621440000000), (268775073/10485760000000), (810421219/26214400000000), (276618913/10485760000000), (42144343/2621440000000), (28752129/4194304000000), (97891017/52428800000000), (12798813/52428800000000)]

theorem checked0602 :
    (∀ i, 0 ≤ plusWeights0602 i) ∧
    (∀ i, 0 ≤ minusWeights0602 i) ∧
    (∀ i, plusCoefficients coefficients0602 upper0602 i = powerCoefficients10 plusWeights0602 i) ∧
    (∀ i, minusCoefficients coefficients0602 upper0602 i = powerCoefficients10 minusWeights0602 i) := by
  decide +kernel

theorem bound0602 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0602 g| ≤ (upper0602 : ℝ) :=
  abs_of_coefficients coefficients0602 upper0602 powerCoefficients10 plusWeights0602 minusWeights0602
    checked0602.1 checked0602.2.1 checked0602.2.2.1 checked0602.2.2.2
    (power_identity10 plusWeights0602) (power_identity10 minusWeights0602) g hg hmax

def envelope0602 : Envelope := ⟨coefficients0602, upper0602, bound0602⟩

def coefficients0603 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-7/512), (-11/1024), (-179/8192), (-67/4096), (-35/4096), (-75/32768)]

def upper0603 : ℚ := (1963699/13107200000000)

def plusWeights0603 : Fin 11 → ℚ := ![(1963699/13107200000000), (1963699/1310720000000), (17673291/2621440000000), (5891097/327680000000), (41237679/1310720000000), (123265037/3276800000000), (40327599/1310720000000), (5428301/327680000000), (69513591/13107200000000), (1002347/1310720000000), 0]

def minusWeights0603 : Fin 11 → ℚ := ![(1963699/13107200000000), (1963699/1310720000000), (17673291/2621440000000), (5891097/327680000000), (41237679/1310720000000), (124161037/3276800000000), (42147759/1310720000000), (6353893/327680000000), (107219319/13107200000000), (2925051/1310720000000), (1963699/6553600000000)]

theorem checked0603 :
    (∀ i, 0 ≤ plusWeights0603 i) ∧
    (∀ i, 0 ≤ minusWeights0603 i) ∧
    (∀ i, plusCoefficients coefficients0603 upper0603 i = powerCoefficients10 plusWeights0603 i) ∧
    (∀ i, minusCoefficients coefficients0603 upper0603 i = powerCoefficients10 minusWeights0603 i) := by
  decide +kernel

theorem bound0603 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0603 g| ≤ (upper0603 : ℝ) :=
  abs_of_coefficients coefficients0603 upper0603 powerCoefficients10 plusWeights0603 minusWeights0603
    checked0603.1 checked0603.2.1 checked0603.2.2.1 checked0603.2.2.2
    (power_identity10 plusWeights0603) (power_identity10 minusWeights0603) g hg hmax

def envelope0603 : Envelope := ⟨coefficients0603, upper0603, bound0603⟩

def coefficients0604 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-7/512), (-11/1024), (-149/8192), (-13/1024), (-425/65536), (-225/131072)]

def upper0604 : ℚ := (1566713/10485760000000)

def plusWeights0604 : Fin 11 → ℚ := ![(1566713/10485760000000), (1566713/1048576000000), (14100417/2097152000000), (4700139/262144000000), (32900973/1048576000000), (98344519/2621440000000), (32172909/1048576000000), (21649991/1310720000000), (277158489/52428800000000), (19971559/26214400000000), 0]

def minusWeights0604 : Fin 11 → ℚ := ![(1566713/10485760000000), (1566713/1048576000000), (14100417/2097152000000), (4700139/262144000000), (32900973/1048576000000), (99061319/2621440000000), (33629037/1048576000000), (25351399/1310720000000), (427862361/52428800000000), (58364091/26214400000000), (1566713/5242880000000)]

theorem checked0604 :
    (∀ i, 0 ≤ plusWeights0604 i) ∧
    (∀ i, 0 ≤ minusWeights0604 i) ∧
    (∀ i, plusCoefficients coefficients0604 upper0604 i = powerCoefficients10 plusWeights0604 i) ∧
    (∀ i, minusCoefficients coefficients0604 upper0604 i = powerCoefficients10 minusWeights0604 i) := by
  decide +kernel

theorem bound0604 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0604 g| ≤ (upper0604 : ℝ) :=
  abs_of_coefficients coefficients0604 upper0604 powerCoefficients10 plusWeights0604 minusWeights0604
    checked0604.1 checked0604.2.1 checked0604.2.2.1 checked0604.2.2.2
    (power_identity10 plusWeights0604) (power_identity10 minusWeights0604) g hg hmax

def envelope0604 : Envelope := ⟨coefficients0604, upper0604, bound0604⟩

def coefficients0605 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-7/512), (-11/1024), (-139/8192), (-47/4096), (-95/16384), (-25/16384)]

def upper0605 : ℚ := (978311/6553600000000)

def plusWeights0605 : Fin 11 → ℚ := ![(978311/6553600000000), (978311/655360000000), (8804799/1310720000000), (2934933/163840000000), (20544531/655360000000), (61409593/1638400000000), (20089491/655360000000), (540723/32768000000), (34607483/6553600000000), (311663/409600000000), 0]

def minusWeights0605 : Fin 11 → ℚ := ![(978311/6553600000000), (978311/655360000000), (8804799/1310720000000), (2934933/163840000000), (20544531/655360000000), (61857593/1638400000000), (20999571/655360000000), (3166251/163840000000), (53440507/6553600000000), (3644903/1638400000000), (978311/3276800000000)]

theorem checked0605 :
    (∀ i, 0 ≤ plusWeights0605 i) ∧
    (∀ i, 0 ≤ minusWeights0605 i) ∧
    (∀ i, plusCoefficients coefficients0605 upper0605 i = powerCoefficients10 plusWeights0605 i) ∧
    (∀ i, minusCoefficients coefficients0605 upper0605 i = powerCoefficients10 minusWeights0605 i) := by
  decide +kernel

theorem bound0605 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0605 g| ≤ (upper0605 : ℝ) :=
  abs_of_coefficients coefficients0605 upper0605 powerCoefficients10 plusWeights0605 minusWeights0605
    checked0605.1 checked0605.2.1 checked0605.2.2.1 checked0605.2.2.2
    (power_identity10 plusWeights0605) (power_identity10 minusWeights0605) g hg hmax

def envelope0605 : Envelope := ⟨coefficients0605, upper0605, bound0605⟩

def coefficients0606 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/256), (-29/1024), (-395/8192), (-47/4096), (-1775/65536), (-1555/131072)]

def upper0606 : ℚ := (39445491/262144000000000)

def plusWeights0606 : Fin 11 → ℚ := ![(39445491/262144000000000), (39445491/26214400000000), (355009419/52428800000000), (118336473/6553600000000), (828355311/26214400000000), (2477385933/65536000000000), (812252911/26214400000000), (109882473/6553600000000), (283896203/52428800000000), (4145993/5242880000000), 0]

def minusWeights0606 : Fin 11 → ℚ := ![(39445491/262144000000000), (39445491/26214400000000), (355009419/52428800000000), (118336473/6553600000000), (828355311/26214400000000), (2492745933/65536000000000), (844457711/26214400000000), (126790473/6553600000000), (85224527/10485760000000), (58161017/26214400000000), (39445491/131072000000000)]

theorem checked0606 :
    (∀ i, 0 ≤ plusWeights0606 i) ∧
    (∀ i, 0 ≤ minusWeights0606 i) ∧
    (∀ i, plusCoefficients coefficients0606 upper0606 i = powerCoefficients10 plusWeights0606 i) ∧
    (∀ i, minusCoefficients coefficients0606 upper0606 i = powerCoefficients10 minusWeights0606 i) := by
  decide +kernel

theorem bound0606 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0606 g| ≤ (upper0606 : ℝ) :=
  abs_of_coefficients coefficients0606 upper0606 powerCoefficients10 plusWeights0606 minusWeights0606
    checked0606.1 checked0606.2.1 checked0606.2.2.1 checked0606.2.2.2
    (power_identity10 plusWeights0606) (power_identity10 minusWeights0606) g hg hmax

def envelope0606 : Envelope := ⟨coefficients0606, upper0606, bound0606⟩

def coefficients0607 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, (-3/256), (-29/1024), (-285/8192), (-67/4096), (-1505/65536), (-1205/131072)]

def upper0607 : ℚ := (39105141/262144000000000)

def plusWeights0607 : Fin 11 → ℚ := ![(39105141/262144000000000), (39105141/26214400000000), (351946269/52428800000000), (117315423/6553600000000), (821207961/26214400000000), (2455943883/65536000000000), (805105561/26214400000000), (108870223/6553600000000), (281041693/52428800000000), (20492763/26214400000000), 0]

def minusWeights0607 : Fin 11 → ℚ := ![(39105141/262144000000000), (39105141/26214400000000), (351946269/52428800000000), (117315423/6553600000000), (821207961/26214400000000), (2471303883/65536000000000), (837310361/26214400000000), (125760623/6553600000000), (84570169/10485760000000), (57717519/26214400000000), (39105141/131072000000000)]

theorem checked0607 :
    (∀ i, 0 ≤ plusWeights0607 i) ∧
    (∀ i, 0 ≤ minusWeights0607 i) ∧
    (∀ i, plusCoefficients coefficients0607 upper0607 i = powerCoefficients10 plusWeights0607 i) ∧
    (∀ i, minusCoefficients coefficients0607 upper0607 i = powerCoefficients10 minusWeights0607 i) := by
  decide +kernel

theorem bound0607 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0607 g| ≤ (upper0607 : ℝ) :=
  abs_of_coefficients coefficients0607 upper0607 powerCoefficients10 plusWeights0607 minusWeights0607
    checked0607.1 checked0607.2.1 checked0607.2.2.1 checked0607.2.2.2
    (power_identity10 plusWeights0607) (power_identity10 minusWeights0607) g hg hmax

def envelope0607 : Envelope := ⟨coefficients0607, upper0607, bound0607⟩

end BilayerDressed.CubicQuarticEnvelopes

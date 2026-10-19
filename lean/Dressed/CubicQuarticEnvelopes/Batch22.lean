import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0704 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/2048), (-11/2048), (-117/8192), (-13/2048)]

def upper0704 : ℚ := (20811/40960000000000)

def plusWeights0704 : Fin 11 → ℚ := ![(20811/40960000000000), (20811/4096000000000), (187299/8192000000000), (62433/1024000000000), (437031/4096000000000), (1311093/10240000000000), (437031/4096000000000), (61983/1024000000000), (176059/8192000000000), (1193/327680000000), 0]

def minusWeights0704 : Fin 11 → ℚ := ![(20811/40960000000000), (20811/4096000000000), (187299/8192000000000), (62433/1024000000000), (437031/4096000000000), (1311093/10240000000000), (437031/4096000000000), (62883/1024000000000), (198539/8192000000000), (53419/8192000000000), (20811/20480000000000)]

theorem checked0704 :
    (∀ i, 0 ≤ plusWeights0704 i) ∧
    (∀ i, 0 ≤ minusWeights0704 i) ∧
    (∀ i, plusCoefficients coefficients0704 upper0704 i = powerCoefficients10 plusWeights0704 i) ∧
    (∀ i, minusCoefficients coefficients0704 upper0704 i = powerCoefficients10 minusWeights0704 i) := by
  decide +kernel

theorem bound0704 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0704 g| ≤ (upper0704 : ℝ) :=
  abs_of_coefficients coefficients0704 upper0704 powerCoefficients10 plusWeights0704 minusWeights0704
    checked0704.1 checked0704.2.1 checked0704.2.2.1 checked0704.2.2.2
    (power_identity10 plusWeights0704) (power_identity10 minusWeights0704) g hg hmax

def envelope0704 : Envelope := ⟨coefficients0704, upper0704, bound0704⟩

def coefficients0705 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/2048), (-11/2048), (-67/8192), (-27/8192)]

def upper0705 : ℚ := (41097/81920000000000)

def plusWeights0705 : Fin 11 → ℚ := ![(41097/81920000000000), (41097/8192000000000), (369873/16384000000000), (123291/2048000000000), (863037/8192000000000), (2589111/20480000000000), (863037/8192000000000), (122391/2048000000000), (347393/16384000000000), (587/163840000000), 0]

def minusWeights0705 : Fin 11 → ℚ := ![(41097/81920000000000), (41097/8192000000000), (369873/16384000000000), (123291/2048000000000), (863037/8192000000000), (2589111/20480000000000), (863037/8192000000000), (124191/2048000000000), (392353/16384000000000), (13211/2048000000000), (41097/40960000000000)]

theorem checked0705 :
    (∀ i, 0 ≤ plusWeights0705 i) ∧
    (∀ i, 0 ≤ minusWeights0705 i) ∧
    (∀ i, plusCoefficients coefficients0705 upper0705 i = powerCoefficients10 plusWeights0705 i) ∧
    (∀ i, minusCoefficients coefficients0705 upper0705 i = powerCoefficients10 minusWeights0705 i) := by
  decide +kernel

theorem bound0705 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0705 g| ≤ (upper0705 : ℝ) :=
  abs_of_coefficients coefficients0705 upper0705 powerCoefficients10 plusWeights0705 minusWeights0705
    checked0705.1 checked0705.2.1 checked0705.2.2.1 checked0705.2.2.2
    (power_identity10 plusWeights0705) (power_identity10 minusWeights0705) g hg hmax

def envelope0705 : Envelope := ⟨coefficients0705, upper0705, bound0705⟩

def coefficients0706 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/2048), (-11/2048), (-21/4096), (-29/16384)]

def upper0706 : ℚ := (81669/163840000000000)

def plusWeights0706 : Fin 11 → ℚ := ![(81669/163840000000000), (81669/16384000000000), (735021/32768000000000), (245007/4096000000000), (1715049/16384000000000), (5145147/40960000000000), (1715049/16384000000000), (243207/4096000000000), (690061/32768000000000), (2329/655360000000), 0]

def minusWeights0706 : Fin 11 → ℚ := ![(81669/163840000000000), (81669/16384000000000), (735021/32768000000000), (245007/4096000000000), (1715049/16384000000000), (5145147/40960000000000), (1715049/16384000000000), (246807/4096000000000), (779981/32768000000000), (105113/16384000000000), (81669/81920000000000)]

theorem checked0706 :
    (∀ i, 0 ≤ plusWeights0706 i) ∧
    (∀ i, 0 ≤ minusWeights0706 i) ∧
    (∀ i, plusCoefficients coefficients0706 upper0706 i = powerCoefficients10 plusWeights0706 i) ∧
    (∀ i, minusCoefficients coefficients0706 upper0706 i = powerCoefficients10 minusWeights0706 i) := by
  decide +kernel

theorem bound0706 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0706 g| ≤ (upper0706 : ℝ) :=
  abs_of_coefficients coefficients0706 upper0706 powerCoefficients10 plusWeights0706 minusWeights0706
    checked0706.1 checked0706.2.1 checked0706.2.2.1 checked0706.2.2.2
    (power_identity10 plusWeights0706) (power_identity10 minusWeights0706) g hg hmax

def envelope0706 : Envelope := ⟨coefficients0706, upper0706, bound0706⟩

def coefficients0707 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-35/8192), (-5/4096), (-135/32768), (-125/65536)]

def upper0707 : ℚ := (11633/26214400000000)

def plusWeights0707 : Fin 11 → ℚ := ![(11633/26214400000000), (11633/2621440000000), (104697/5242880000000), (34899/655360000000), (244293/2621440000000), (732879/6553600000000), (244293/2621440000000), (34619/655360000000), (97913/5242880000000), (40991/13107200000000), 0]

def minusWeights0707 : Fin 11 → ℚ := ![(11633/26214400000000), (11633/2621440000000), (104697/5242880000000), (34899/655360000000), (244293/2621440000000), (732879/6553600000000), (244293/2621440000000), (35179/655360000000), (111481/5242880000000), (75339/13107200000000), (11633/13107200000000)]

theorem checked0707 :
    (∀ i, 0 ≤ plusWeights0707 i) ∧
    (∀ i, 0 ≤ minusWeights0707 i) ∧
    (∀ i, plusCoefficients coefficients0707 upper0707 i = powerCoefficients10 plusWeights0707 i) ∧
    (∀ i, minusCoefficients coefficients0707 upper0707 i = powerCoefficients10 minusWeights0707 i) := by
  decide +kernel

theorem bound0707 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0707 g| ≤ (upper0707 : ℝ) :=
  abs_of_coefficients coefficients0707 upper0707 powerCoefficients10 plusWeights0707 minusWeights0707
    checked0707.1 checked0707.2.1 checked0707.2.2.1 checked0707.2.2.2
    (power_identity10 plusWeights0707) (power_identity10 minusWeights0707) g hg hmax

def envelope0707 : Envelope := ⟨coefficients0707, upper0707, bound0707⟩

def coefficients0708 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-35/8192), (-5/4096), (-85/32768), (-75/65536)]

def upper0708 : ℚ := (11591/26214400000000)

def plusWeights0708 : Fin 11 → ℚ := ![(11591/26214400000000), (11591/2621440000000), (104319/5242880000000), (34773/655360000000), (243411/2621440000000), (730233/6553600000000), (243411/2621440000000), (34493/655360000000), (19507/1048576000000), (40801/13107200000000), 0]

def minusWeights0708 : Fin 11 → ℚ := ![(11591/26214400000000), (11591/2621440000000), (104319/5242880000000), (34773/655360000000), (243411/2621440000000), (730233/6553600000000), (243411/2621440000000), (35053/655360000000), (111103/5242880000000), (75109/13107200000000), (11591/13107200000000)]

theorem checked0708 :
    (∀ i, 0 ≤ plusWeights0708 i) ∧
    (∀ i, 0 ≤ minusWeights0708 i) ∧
    (∀ i, plusCoefficients coefficients0708 upper0708 i = powerCoefficients10 plusWeights0708 i) ∧
    (∀ i, minusCoefficients coefficients0708 upper0708 i = powerCoefficients10 minusWeights0708 i) := by
  decide +kernel

theorem bound0708 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0708 g| ≤ (upper0708 : ℝ) :=
  abs_of_coefficients coefficients0708 upper0708 powerCoefficients10 plusWeights0708 minusWeights0708
    checked0708.1 checked0708.2.1 checked0708.2.2.1 checked0708.2.2.2
    (power_identity10 plusWeights0708) (power_identity10 minusWeights0708) g hg hmax

def envelope0708 : Envelope := ⟨coefficients0708, upper0708, bound0708⟩

def coefficients0709 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-25/8192), 0, (-125/65536), (-125/131072)]

def upper0709 : ℚ := (3221/10485760000000)

def plusWeights0709 : Fin 11 → ℚ := ![(3221/10485760000000), (3221/1048576000000), (28989/2097152000000), (9663/262144000000), (67641/1048576000000), (202923/2621440000000), (67641/1048576000000), (9583/262144000000), (27069/2097152000000), (2259/1048576000000), 0]

def minusWeights0709 : Fin 11 → ℚ := ![(3221/10485760000000), (3221/1048576000000), (28989/2097152000000), (9663/262144000000), (67641/1048576000000), (202923/2621440000000), (67641/1048576000000), (9743/262144000000), (30909/2097152000000), (4183/1048576000000), (3221/5242880000000)]

theorem checked0709 :
    (∀ i, 0 ≤ plusWeights0709 i) ∧
    (∀ i, 0 ≤ minusWeights0709 i) ∧
    (∀ i, plusCoefficients coefficients0709 upper0709 i = powerCoefficients10 plusWeights0709 i) ∧
    (∀ i, minusCoefficients coefficients0709 upper0709 i = powerCoefficients10 minusWeights0709 i) := by
  decide +kernel

theorem bound0709 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0709 g| ≤ (upper0709 : ℝ) :=
  abs_of_coefficients coefficients0709 upper0709 powerCoefficients10 plusWeights0709 minusWeights0709
    checked0709.1 checked0709.2.1 checked0709.2.2.1 checked0709.2.2.2
    (power_identity10 plusWeights0709) (power_identity10 minusWeights0709) g hg hmax

def envelope0709 : Envelope := ⟨coefficients0709, upper0709, bound0709⟩

def coefficients0710 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-25/8192), (125/32768), (125/65536), (625/524288)]

def upper0710 : ℚ := (2223/8388608000000)

def plusWeights0710 : Fin 11 → ℚ := ![(2223/8388608000000), (2223/838860800000), (20007/1677721600000), (6669/209715200000), (46683/838860800000), (140049/2097152000000), (46683/838860800000), (1321/41943040000), (3707/335544320000), (7603/4194304000000), 0]

def minusWeights0710 : Fin 11 → ℚ := ![(2223/8388608000000), (2223/838860800000), (20007/1677721600000), (6669/209715200000), (46683/838860800000), (140049/2097152000000), (46683/838860800000), (6733/209715200000), (21479/1677721600000), (14627/4194304000000), (2223/4194304000000)]

theorem checked0710 :
    (∀ i, 0 ≤ plusWeights0710 i) ∧
    (∀ i, 0 ≤ minusWeights0710 i) ∧
    (∀ i, plusCoefficients coefficients0710 upper0710 i = powerCoefficients10 plusWeights0710 i) ∧
    (∀ i, minusCoefficients coefficients0710 upper0710 i = powerCoefficients10 minusWeights0710 i) := by
  decide +kernel

theorem bound0710 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0710 g| ≤ (upper0710 : ℝ) :=
  abs_of_coefficients coefficients0710 upper0710 powerCoefficients10 plusWeights0710 minusWeights0710
    checked0710.1 checked0710.2.1 checked0710.2.2.1 checked0710.2.2.2
    (power_identity10 plusWeights0710) (power_identity10 minusWeights0710) g hg hmax

def envelope0710 : Envelope := ⟨coefficients0710, upper0710, bound0710⟩

def coefficients0711 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-25/8192), (175/32768), (175/65536), (3875/524288)]

def upper0711 : ℚ := (10417/41943040000000)

def plusWeights0711 : Fin 11 → ℚ := ![(10417/41943040000000), (10417/4194304000000), (93753/8388608000000), (31251/1048576000000), (218757/4194304000000), (656271/10485760000000), (218757/4194304000000), (30931/1048576000000), (86521/8388608000000), (35181/20971520000000), 0]

def minusWeights0711 : Fin 11 → ℚ := ![(10417/41943040000000), (10417/4194304000000), (93753/8388608000000), (31251/1048576000000), (218757/4194304000000), (656271/10485760000000), (218757/4194304000000), (31571/1048576000000), (20197/1677721600000), (68989/20971520000000), (10417/20971520000000)]

theorem checked0711 :
    (∀ i, 0 ≤ plusWeights0711 i) ∧
    (∀ i, 0 ≤ minusWeights0711 i) ∧
    (∀ i, plusCoefficients coefficients0711 upper0711 i = powerCoefficients10 plusWeights0711 i) ∧
    (∀ i, minusCoefficients coefficients0711 upper0711 i = powerCoefficients10 minusWeights0711 i) := by
  decide +kernel

theorem bound0711 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0711 g| ≤ (upper0711 : ℝ) :=
  abs_of_coefficients coefficients0711 upper0711 powerCoefficients10 plusWeights0711 minusWeights0711
    checked0711.1 checked0711.2.1 checked0711.2.2.1 checked0711.2.2.2
    (power_identity10 plusWeights0711) (power_identity10 minusWeights0711) g hg hmax

def envelope0711 : Envelope := ⟨coefficients0711, upper0711, bound0711⟩

def coefficients0712 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/2048), (-5/2048), (-55/8192), (-25/8192)]

def upper0712 : ℚ := (903/3276800000000)

def plusWeights0712 : Fin 11 → ℚ := ![(903/3276800000000), (903/327680000000), (8127/655360000000), (2709/81920000000), (18963/327680000000), (56889/819200000000), (18963/327680000000), (2689/81920000000), (7631/655360000000), (403/204800000000), 0]

def minusWeights0712 : Fin 11 → ℚ := ![(903/3276800000000), (903/327680000000), (8127/655360000000), (2709/81920000000), (18963/327680000000), (56889/819200000000), (18963/327680000000), (2729/81920000000), (8623/655360000000), (2903/819200000000), (903/1638400000000)]

theorem checked0712 :
    (∀ i, 0 ≤ plusWeights0712 i) ∧
    (∀ i, 0 ≤ minusWeights0712 i) ∧
    (∀ i, plusCoefficients coefficients0712 upper0712 i = powerCoefficients10 plusWeights0712 i) ∧
    (∀ i, minusCoefficients coefficients0712 upper0712 i = powerCoefficients10 minusWeights0712 i) := by
  decide +kernel

theorem bound0712 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0712 g| ≤ (upper0712 : ℝ) :=
  abs_of_coefficients coefficients0712 upper0712 powerCoefficients10 plusWeights0712 minusWeights0712
    checked0712.1 checked0712.2.1 checked0712.2.2.1 checked0712.2.2.2
    (power_identity10 plusWeights0712) (power_identity10 minusWeights0712) g hg hmax

def envelope0712 : Envelope := ⟨coefficients0712, upper0712, bound0712⟩

def coefficients0713 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/2048), (-5/2048), (-145/32768), (-125/65536)]

def upper0713 : ℚ := (7161/26214400000000)

def plusWeights0713 : Fin 11 → ℚ := ![(7161/26214400000000), (7161/2621440000000), (64449/5242880000000), (21483/655360000000), (150381/2621440000000), (451143/6553600000000), (150381/2621440000000), (21323/655360000000), (60481/5242880000000), (25507/13107200000000), 0]

def minusWeights0713 : Fin 11 → ℚ := ![(7161/26214400000000), (7161/2621440000000), (64449/5242880000000), (21483/655360000000), (150381/2621440000000), (451143/6553600000000), (150381/2621440000000), (21643/655360000000), (68417/5242880000000), (46103/13107200000000), (7161/13107200000000)]

theorem checked0713 :
    (∀ i, 0 ≤ plusWeights0713 i) ∧
    (∀ i, 0 ≤ minusWeights0713 i) ∧
    (∀ i, plusCoefficients coefficients0713 upper0713 i = powerCoefficients10 plusWeights0713 i) ∧
    (∀ i, minusCoefficients coefficients0713 upper0713 i = powerCoefficients10 minusWeights0713 i) := by
  decide +kernel

theorem bound0713 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0713 g| ≤ (upper0713 : ℝ) :=
  abs_of_coefficients coefficients0713 upper0713 powerCoefficients10 plusWeights0713 minusWeights0713
    checked0713.1 checked0713.2.1 checked0713.2.2.1 checked0713.2.2.2
    (power_identity10 plusWeights0713) (power_identity10 minusWeights0713) g hg hmax

def envelope0713 : Envelope := ⟨coefficients0713, upper0713, bound0713⟩

def coefficients0714 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-5/2048), (-5/2048), (-45/32768), (-25/65536)]

def upper0714 : ℚ := (7077/26214400000000)

def plusWeights0714 : Fin 11 → ℚ := ![(7077/26214400000000), (7077/2621440000000), (63693/5242880000000), (21231/655360000000), (148617/2621440000000), (445851/6553600000000), (148617/2621440000000), (21071/655360000000), (2389/209715200000), (25127/13107200000000), 0]

def minusWeights0714 : Fin 11 → ℚ := ![(7077/26214400000000), (7077/2621440000000), (63693/5242880000000), (21231/655360000000), (148617/2621440000000), (445851/6553600000000), (148617/2621440000000), (21391/655360000000), (67661/5242880000000), (45643/13107200000000), (7077/13107200000000)]

theorem checked0714 :
    (∀ i, 0 ≤ plusWeights0714 i) ∧
    (∀ i, 0 ≤ minusWeights0714 i) ∧
    (∀ i, plusCoefficients coefficients0714 upper0714 i = powerCoefficients10 plusWeights0714 i) ∧
    (∀ i, minusCoefficients coefficients0714 upper0714 i = powerCoefficients10 minusWeights0714 i) := by
  decide +kernel

theorem bound0714 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0714 g| ≤ (upper0714 : ℝ) :=
  abs_of_coefficients coefficients0714 upper0714 powerCoefficients10 plusWeights0714 minusWeights0714
    checked0714.1 checked0714.2.1 checked0714.2.2.1 checked0714.2.2.2
    (power_identity10 plusWeights0714) (power_identity10 minusWeights0714) g hg hmax

def envelope0714 : Envelope := ⟨coefficients0714, upper0714, bound0714⟩

def coefficients0715 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/4096), (-11/4096), (-209/32768), (-183/65536)]

def upper0715 : ℚ := (165963/655360000000000)

def plusWeights0715 : Fin 11 → ℚ := ![(165963/655360000000000), (165963/65536000000000), (1493667/131072000000000), (497889/16384000000000), (3485223/65536000000000), (10455669/163840000000000), (3485223/65536000000000), (494289/16384000000000), (1403747/131072000000000), (4753/2621440000000), 0]

def minusWeights0715 : Fin 11 → ℚ := ![(165963/655360000000000), (165963/65536000000000), (1493667/131072000000000), (497889/16384000000000), (3485223/65536000000000), (10455669/163840000000000), (3485223/65536000000000), (501489/16384000000000), (1583587/131072000000000), (213101/65536000000000), (165963/327680000000000)]

theorem checked0715 :
    (∀ i, 0 ≤ plusWeights0715 i) ∧
    (∀ i, 0 ≤ minusWeights0715 i) ∧
    (∀ i, plusCoefficients coefficients0715 upper0715 i = powerCoefficients10 plusWeights0715 i) ∧
    (∀ i, minusCoefficients coefficients0715 upper0715 i = powerCoefficients10 minusWeights0715 i) := by
  decide +kernel

theorem bound0715 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0715 g| ≤ (upper0715 : ℝ) :=
  abs_of_coefficients coefficients0715 upper0715 powerCoefficients10 plusWeights0715 minusWeights0715
    checked0715.1 checked0715.2.1 checked0715.2.2.1 checked0715.2.2.2
    (power_identity10 plusWeights0715) (power_identity10 minusWeights0715) g hg hmax

def envelope0715 : Envelope := ⟨coefficients0715, upper0715, bound0715⟩

def coefficients0716 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-9/4096), (-11/4096), (-67/16384), (-27/16384)]

def upper0716 : ℚ := (41097/163840000000000)

def plusWeights0716 : Fin 11 → ℚ := ![(41097/163840000000000), (41097/16384000000000), (369873/32768000000000), (123291/4096000000000), (863037/16384000000000), (2589111/40960000000000), (863037/16384000000000), (122391/4096000000000), (347393/32768000000000), (587/327680000000), 0]

def minusWeights0716 : Fin 11 → ℚ := ![(41097/163840000000000), (41097/16384000000000), (369873/32768000000000), (123291/4096000000000), (863037/16384000000000), (2589111/40960000000000), (863037/16384000000000), (124191/4096000000000), (392353/32768000000000), (13211/4096000000000), (41097/81920000000000)]

theorem checked0716 :
    (∀ i, 0 ≤ plusWeights0716 i) ∧
    (∀ i, 0 ≤ minusWeights0716 i) ∧
    (∀ i, plusCoefficients coefficients0716 upper0716 i = powerCoefficients10 plusWeights0716 i) ∧
    (∀ i, minusCoefficients coefficients0716 upper0716 i = powerCoefficients10 minusWeights0716 i) := by
  decide +kernel

theorem bound0716 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0716 g| ≤ (upper0716 : ℝ) :=
  abs_of_coefficients coefficients0716 upper0716 powerCoefficients10 plusWeights0716 minusWeights0716
    checked0716.1 checked0716.2.1 checked0716.2.2.1 checked0716.2.2.2
    (power_identity10 plusWeights0716) (power_identity10 minusWeights0716) g hg hmax

def envelope0716 : Envelope := ⟨coefficients0716, upper0716, bound0716⟩

def coefficients0717 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, (-15/8192), (15/2048), (-105/65536), (-225/131072)]

def upper0717 : ℚ := (5853/52428800000000)

def plusWeights0717 : Fin 11 → ℚ := ![(5853/52428800000000), (5853/5242880000000), (52677/10485760000000), (17559/1310720000000), (122913/5242880000000), (368739/13107200000000), (122913/5242880000000), (17319/1310720000000), (9537/2097152000000), (18663/26214400000000), 0]

def minusWeights0717 : Fin 11 → ℚ := ![(5853/52428800000000), (5853/5242880000000), (52677/10485760000000), (17559/1310720000000), (122913/5242880000000), (368739/13107200000000), (122913/5242880000000), (17799/1310720000000), (57669/10485760000000), (39867/26214400000000), (5853/26214400000000)]

theorem checked0717 :
    (∀ i, 0 ≤ plusWeights0717 i) ∧
    (∀ i, 0 ≤ minusWeights0717 i) ∧
    (∀ i, plusCoefficients coefficients0717 upper0717 i = powerCoefficients10 plusWeights0717 i) ∧
    (∀ i, minusCoefficients coefficients0717 upper0717 i = powerCoefficients10 minusWeights0717 i) := by
  decide +kernel

theorem bound0717 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0717 g| ≤ (upper0717 : ℝ) :=
  abs_of_coefficients coefficients0717 upper0717 powerCoefficients10 plusWeights0717 minusWeights0717
    checked0717.1 checked0717.2.1 checked0717.2.2.1 checked0717.2.2.2
    (power_identity10 plusWeights0717) (power_identity10 minusWeights0717) g hg hmax

def envelope0717 : Envelope := ⟨coefficients0717, upper0717, bound0717⟩

def coefficients0718 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-375/32768), (-375/65536), (-1875/524288)]

def upper0718 : ℚ := (1011/8388608000000)

def plusWeights0718 : Fin 11 → ℚ := ![(1011/8388608000000), (1011/838860800000), (9099/1677721600000), (3033/209715200000), (21231/838860800000), (63693/2097152000000), (21231/838860800000), (3033/209715200000), (8907/1677721600000), (4071/4194304000000), 0]

def minusWeights0718 : Fin 11 → ℚ := ![(1011/8388608000000), (1011/838860800000), (9099/1677721600000), (3033/209715200000), (21231/838860800000), (63693/2097152000000), (21231/838860800000), (3033/209715200000), (9291/1677721600000), (6039/4194304000000), (1011/4194304000000)]

theorem checked0718 :
    (∀ i, 0 ≤ plusWeights0718 i) ∧
    (∀ i, 0 ≤ minusWeights0718 i) ∧
    (∀ i, plusCoefficients coefficients0718 upper0718 i = powerCoefficients10 plusWeights0718 i) ∧
    (∀ i, minusCoefficients coefficients0718 upper0718 i = powerCoefficients10 minusWeights0718 i) := by
  decide +kernel

theorem bound0718 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0718 g| ≤ (upper0718 : ℝ) :=
  abs_of_coefficients coefficients0718 upper0718 powerCoefficients10 plusWeights0718 minusWeights0718
    checked0718.1 checked0718.2.1 checked0718.2.2.1 checked0718.2.2.2
    (power_identity10 plusWeights0718) (power_identity10 minusWeights0718) g hg hmax

def envelope0718 : Envelope := ⟨coefficients0718, upper0718, bound0718⟩

def coefficients0719 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-225/32768), (-225/65536), (-1125/524288)]

def upper0719 : ℚ := (3033/41943040000000)

def plusWeights0719 : Fin 11 → ℚ := ![(3033/41943040000000), (3033/4194304000000), (27297/8388608000000), (9099/1048576000000), (63693/4194304000000), (191079/10485760000000), (63693/4194304000000), (9099/1048576000000), (26721/8388608000000), (12213/20971520000000), 0]

def minusWeights0719 : Fin 11 → ℚ := ![(3033/41943040000000), (3033/4194304000000), (27297/8388608000000), (9099/1048576000000), (63693/4194304000000), (191079/10485760000000), (63693/4194304000000), (9099/1048576000000), (27873/8388608000000), (18117/20971520000000), (3033/20971520000000)]

theorem checked0719 :
    (∀ i, 0 ≤ plusWeights0719 i) ∧
    (∀ i, 0 ≤ minusWeights0719 i) ∧
    (∀ i, plusCoefficients coefficients0719 upper0719 i = powerCoefficients10 plusWeights0719 i) ∧
    (∀ i, minusCoefficients coefficients0719 upper0719 i = powerCoefficients10 minusWeights0719 i) := by
  decide +kernel

theorem bound0719 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0719 g| ≤ (upper0719 : ℝ) :=
  abs_of_coefficients coefficients0719 upper0719 powerCoefficients10 plusWeights0719 minusWeights0719
    checked0719.1 checked0719.2.1 checked0719.2.2.1 checked0719.2.2.2
    (power_identity10 plusWeights0719) (power_identity10 minusWeights0719) g hg hmax

def envelope0719 : Envelope := ⟨coefficients0719, upper0719, bound0719⟩

def coefficients0720 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-225/32768), (-225/65536), (3375/524288)]

def upper0720 : ℚ := (2997/41943040000000)

def plusWeights0720 : Fin 11 → ℚ := ![(2997/41943040000000), (2997/4194304000000), (26973/8388608000000), (8991/1048576000000), (62937/4194304000000), (188811/10485760000000), (62937/4194304000000), (8991/1048576000000), (26397/8388608000000), (12033/20971520000000), 0]

def minusWeights0720 : Fin 11 → ℚ := ![(2997/41943040000000), (2997/4194304000000), (26973/8388608000000), (8991/1048576000000), (62937/4194304000000), (188811/10485760000000), (62937/4194304000000), (8991/1048576000000), (27549/8388608000000), (17937/20971520000000), (2997/20971520000000)]

theorem checked0720 :
    (∀ i, 0 ≤ plusWeights0720 i) ∧
    (∀ i, 0 ≤ minusWeights0720 i) ∧
    (∀ i, plusCoefficients coefficients0720 upper0720 i = powerCoefficients10 plusWeights0720 i) ∧
    (∀ i, minusCoefficients coefficients0720 upper0720 i = powerCoefficients10 minusWeights0720 i) := by
  decide +kernel

theorem bound0720 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0720 g| ≤ (upper0720 : ℝ) :=
  abs_of_coefficients coefficients0720 upper0720 powerCoefficients10 plusWeights0720 minusWeights0720
    checked0720.1 checked0720.2.1 checked0720.2.2.1 checked0720.2.2.2
    (power_identity10 plusWeights0720) (power_identity10 minusWeights0720) g hg hmax

def envelope0720 : Envelope := ⟨coefficients0720, upper0720, bound0720⟩

def coefficients0721 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (-75/32768), (-75/65536), (-375/524288)]

def upper0721 : ℚ := (1011/41943040000000)

def plusWeights0721 : Fin 11 → ℚ := ![(1011/41943040000000), (1011/4194304000000), (9099/8388608000000), (3033/1048576000000), (21231/4194304000000), (63693/10485760000000), (21231/4194304000000), (3033/1048576000000), (8907/8388608000000), (4071/20971520000000), 0]

def minusWeights0721 : Fin 11 → ℚ := ![(1011/41943040000000), (1011/4194304000000), (9099/8388608000000), (3033/1048576000000), (21231/4194304000000), (63693/10485760000000), (21231/4194304000000), (3033/1048576000000), (9291/8388608000000), (6039/20971520000000), (1011/20971520000000)]

theorem checked0721 :
    (∀ i, 0 ≤ plusWeights0721 i) ∧
    (∀ i, 0 ≤ minusWeights0721 i) ∧
    (∀ i, plusCoefficients coefficients0721 upper0721 i = powerCoefficients10 plusWeights0721 i) ∧
    (∀ i, minusCoefficients coefficients0721 upper0721 i = powerCoefficients10 minusWeights0721 i) := by
  decide +kernel

theorem bound0721 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0721 g| ≤ (upper0721 : ℝ) :=
  abs_of_coefficients coefficients0721 upper0721 powerCoefficients10 plusWeights0721 minusWeights0721
    checked0721.1 checked0721.2.1 checked0721.2.2.1 checked0721.2.2.2
    (power_identity10 plusWeights0721) (power_identity10 minusWeights0721) g hg hmax

def envelope0721 : Envelope := ⟨coefficients0721, upper0721, bound0721⟩

def coefficients0722 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-1125/32768), (-1125/65536)]

def upper0722 : ℚ := (189/5242880000000)

def plusWeights0722 : Fin 11 → ℚ := ![(189/5242880000000), (189/524288000000), (1701/1048576000000), (567/131072000000), (3969/524288000000), (11907/1310720000000), (3969/524288000000), (567/131072000000), (1701/1048576000000), (171/524288000000), 0]

def minusWeights0722 : Fin 11 → ℚ := ![(189/5242880000000), (189/524288000000), (1701/1048576000000), (567/131072000000), (3969/524288000000), (11907/1310720000000), (3969/524288000000), (567/131072000000), (1701/1048576000000), (207/524288000000), (189/2621440000000)]

theorem checked0722 :
    (∀ i, 0 ≤ plusWeights0722 i) ∧
    (∀ i, 0 ≤ minusWeights0722 i) ∧
    (∀ i, plusCoefficients coefficients0722 upper0722 i = powerCoefficients10 plusWeights0722 i) ∧
    (∀ i, minusCoefficients coefficients0722 upper0722 i = powerCoefficients10 minusWeights0722 i) := by
  decide +kernel

theorem bound0722 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0722 g| ≤ (upper0722 : ℝ) :=
  abs_of_coefficients coefficients0722 upper0722 powerCoefficients10 plusWeights0722 minusWeights0722
    checked0722.1 checked0722.2.1 checked0722.2.2.1 checked0722.2.2.2
    (power_identity10 plusWeights0722) (power_identity10 minusWeights0722) g hg hmax

def envelope0722 : Envelope := ⟨coefficients0722, upper0722, bound0722⟩

def coefficients0723 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-975/32768), (-975/65536)]

def upper0723 : ℚ := (819/26214400000000)

def plusWeights0723 : Fin 11 → ℚ := ![(819/26214400000000), (819/2621440000000), (7371/5242880000000), (2457/655360000000), (17199/2621440000000), (51597/6553600000000), (17199/2621440000000), (2457/655360000000), (7371/5242880000000), (741/2621440000000), 0]

def minusWeights0723 : Fin 11 → ℚ := ![(819/26214400000000), (819/2621440000000), (7371/5242880000000), (2457/655360000000), (17199/2621440000000), (51597/6553600000000), (17199/2621440000000), (2457/655360000000), (7371/5242880000000), (897/2621440000000), (819/13107200000000)]

theorem checked0723 :
    (∀ i, 0 ≤ plusWeights0723 i) ∧
    (∀ i, 0 ≤ minusWeights0723 i) ∧
    (∀ i, plusCoefficients coefficients0723 upper0723 i = powerCoefficients10 plusWeights0723 i) ∧
    (∀ i, minusCoefficients coefficients0723 upper0723 i = powerCoefficients10 minusWeights0723 i) := by
  decide +kernel

theorem bound0723 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0723 g| ≤ (upper0723 : ℝ) :=
  abs_of_coefficients coefficients0723 upper0723 powerCoefficients10 plusWeights0723 minusWeights0723
    checked0723.1 checked0723.2.1 checked0723.2.2.1 checked0723.2.2.2
    (power_identity10 plusWeights0723) (power_identity10 minusWeights0723) g hg hmax

def envelope0723 : Envelope := ⟨coefficients0723, upper0723, bound0723⟩

def coefficients0724 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-275/16384), (-275/32768)]

def upper0724 : ℚ := (231/13107200000000)

def plusWeights0724 : Fin 11 → ℚ := ![(231/13107200000000), (231/1310720000000), (2079/2621440000000), (693/327680000000), (4851/1310720000000), (14553/3276800000000), (4851/1310720000000), (693/327680000000), (2079/2621440000000), (209/1310720000000), 0]

def minusWeights0724 : Fin 11 → ℚ := ![(231/13107200000000), (231/1310720000000), (2079/2621440000000), (693/327680000000), (4851/1310720000000), (14553/3276800000000), (4851/1310720000000), (693/327680000000), (2079/2621440000000), (253/1310720000000), (231/6553600000000)]

theorem checked0724 :
    (∀ i, 0 ≤ plusWeights0724 i) ∧
    (∀ i, 0 ≤ minusWeights0724 i) ∧
    (∀ i, plusCoefficients coefficients0724 upper0724 i = powerCoefficients10 plusWeights0724 i) ∧
    (∀ i, minusCoefficients coefficients0724 upper0724 i = powerCoefficients10 minusWeights0724 i) := by
  decide +kernel

theorem bound0724 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0724 g| ≤ (upper0724 : ℝ) :=
  abs_of_coefficients coefficients0724 upper0724 powerCoefficients10 plusWeights0724 minusWeights0724
    checked0724.1 checked0724.2.1 checked0724.2.2.1 checked0724.2.2.2
    (power_identity10 plusWeights0724) (power_identity10 minusWeights0724) g hg hmax

def envelope0724 : Envelope := ⟨coefficients0724, upper0724, bound0724⟩

def coefficients0725 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-175/16384), (-175/32768)]

def upper0725 : ℚ := (147/13107200000000)

def plusWeights0725 : Fin 11 → ℚ := ![(147/13107200000000), (147/1310720000000), (1323/2621440000000), (441/327680000000), (3087/1310720000000), (9261/3276800000000), (3087/1310720000000), (441/327680000000), (1323/2621440000000), (133/1310720000000), 0]

def minusWeights0725 : Fin 11 → ℚ := ![(147/13107200000000), (147/1310720000000), (1323/2621440000000), (441/327680000000), (3087/1310720000000), (9261/3276800000000), (3087/1310720000000), (441/327680000000), (1323/2621440000000), (161/1310720000000), (147/6553600000000)]

theorem checked0725 :
    (∀ i, 0 ≤ plusWeights0725 i) ∧
    (∀ i, 0 ≤ minusWeights0725 i) ∧
    (∀ i, plusCoefficients coefficients0725 upper0725 i = powerCoefficients10 plusWeights0725 i) ∧
    (∀ i, minusCoefficients coefficients0725 upper0725 i = powerCoefficients10 minusWeights0725 i) := by
  decide +kernel

theorem bound0725 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0725 g| ≤ (upper0725 : ℝ) :=
  abs_of_coefficients coefficients0725 upper0725 powerCoefficients10 plusWeights0725 minusWeights0725
    checked0725.1 checked0725.2.1 checked0725.2.2.1 checked0725.2.2.2
    (power_identity10 plusWeights0725) (power_identity10 minusWeights0725) g hg hmax

def envelope0725 : Envelope := ⟨coefficients0725, upper0725, bound0725⟩

def coefficients0726 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-75/32768), (-75/65536)]

def upper0726 : ℚ := (63/26214400000000)

def plusWeights0726 : Fin 11 → ℚ := ![(63/26214400000000), (63/2621440000000), (567/5242880000000), (189/655360000000), (1323/2621440000000), (3969/6553600000000), (1323/2621440000000), (189/655360000000), (567/5242880000000), (57/2621440000000), 0]

def minusWeights0726 : Fin 11 → ℚ := ![(63/26214400000000), (63/2621440000000), (567/5242880000000), (189/655360000000), (1323/2621440000000), (3969/6553600000000), (1323/2621440000000), (189/655360000000), (567/5242880000000), (69/2621440000000), (63/13107200000000)]

theorem checked0726 :
    (∀ i, 0 ≤ plusWeights0726 i) ∧
    (∀ i, 0 ≤ minusWeights0726 i) ∧
    (∀ i, plusCoefficients coefficients0726 upper0726 i = powerCoefficients10 plusWeights0726 i) ∧
    (∀ i, minusCoefficients coefficients0726 upper0726 i = powerCoefficients10 minusWeights0726 i) := by
  decide +kernel

theorem bound0726 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0726 g| ≤ (upper0726 : ℝ) :=
  abs_of_coefficients coefficients0726 upper0726 powerCoefficients10 plusWeights0726 minusWeights0726
    checked0726.1 checked0726.2.1 checked0726.2.2.1 checked0726.2.2.2
    (power_identity10 plusWeights0726) (power_identity10 minusWeights0726) g hg hmax

def envelope0726 : Envelope := ⟨coefficients0726, upper0726, bound0726⟩

def coefficients0727 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (-25/32768), (-25/65536)]

def upper0727 : ℚ := (21/26214400000000)

def plusWeights0727 : Fin 11 → ℚ := ![(21/26214400000000), (21/2621440000000), (189/5242880000000), (63/655360000000), (441/2621440000000), (1323/6553600000000), (441/2621440000000), (63/655360000000), (189/5242880000000), (19/2621440000000), 0]

def minusWeights0727 : Fin 11 → ℚ := ![(21/26214400000000), (21/2621440000000), (189/5242880000000), (63/655360000000), (441/2621440000000), (1323/6553600000000), (441/2621440000000), (63/655360000000), (189/5242880000000), (23/2621440000000), (21/13107200000000)]

theorem checked0727 :
    (∀ i, 0 ≤ plusWeights0727 i) ∧
    (∀ i, 0 ≤ minusWeights0727 i) ∧
    (∀ i, plusCoefficients coefficients0727 upper0727 i = powerCoefficients10 plusWeights0727 i) ∧
    (∀ i, minusCoefficients coefficients0727 upper0727 i = powerCoefficients10 minusWeights0727 i) := by
  decide +kernel

theorem bound0727 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0727 g| ≤ (upper0727 : ℝ) :=
  abs_of_coefficients coefficients0727 upper0727 powerCoefficients10 plusWeights0727 minusWeights0727
    checked0727.1 checked0727.2.1 checked0727.2.2.1 checked0727.2.2.2
    (power_identity10 plusWeights0727) (power_identity10 minusWeights0727) g hg hmax

def envelope0727 : Envelope := ⟨coefficients0727, upper0727, bound0727⟩

def coefficients0728 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (125/262144)]

def upper0728 : ℚ := (1/20971520000000)

def plusWeights0728 : Fin 11 → ℚ := ![(1/20971520000000), (1/2097152000000), (9/4194304000000), (3/524288000000), (21/2097152000000), (63/5242880000000), (21/2097152000000), (3/524288000000), (9/4194304000000), (1/2097152000000), (1/10485760000000)]

def minusWeights0728 : Fin 11 → ℚ := ![(1/20971520000000), (1/2097152000000), (9/4194304000000), (3/524288000000), (21/2097152000000), (63/5242880000000), (21/2097152000000), (3/524288000000), (9/4194304000000), (1/2097152000000), 0]

theorem checked0728 :
    (∀ i, 0 ≤ plusWeights0728 i) ∧
    (∀ i, 0 ≤ minusWeights0728 i) ∧
    (∀ i, plusCoefficients coefficients0728 upper0728 i = powerCoefficients10 plusWeights0728 i) ∧
    (∀ i, minusCoefficients coefficients0728 upper0728 i = powerCoefficients10 minusWeights0728 i) := by
  decide +kernel

theorem bound0728 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0728 g| ≤ (upper0728 : ℝ) :=
  abs_of_coefficients coefficients0728 upper0728 powerCoefficients10 plusWeights0728 minusWeights0728
    checked0728.1 checked0728.2.1 checked0728.2.2.1 checked0728.2.2.2
    (power_identity10 plusWeights0728) (power_identity10 minusWeights0728) g hg hmax

def envelope0728 : Envelope := ⟨coefficients0728, upper0728, bound0728⟩

def coefficients0729 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (125/131072)]

def upper0729 : ℚ := (1/10485760000000)

def plusWeights0729 : Fin 11 → ℚ := ![(1/10485760000000), (1/1048576000000), (9/2097152000000), (3/262144000000), (21/1048576000000), (63/2621440000000), (21/1048576000000), (3/262144000000), (9/2097152000000), (1/1048576000000), (1/5242880000000)]

def minusWeights0729 : Fin 11 → ℚ := ![(1/10485760000000), (1/1048576000000), (9/2097152000000), (3/262144000000), (21/1048576000000), (63/2621440000000), (21/1048576000000), (3/262144000000), (9/2097152000000), (1/1048576000000), 0]

theorem checked0729 :
    (∀ i, 0 ≤ plusWeights0729 i) ∧
    (∀ i, 0 ≤ minusWeights0729 i) ∧
    (∀ i, plusCoefficients coefficients0729 upper0729 i = powerCoefficients10 plusWeights0729 i) ∧
    (∀ i, minusCoefficients coefficients0729 upper0729 i = powerCoefficients10 minusWeights0729 i) := by
  decide +kernel

theorem bound0729 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0729 g| ≤ (upper0729 : ℝ) :=
  abs_of_coefficients coefficients0729 upper0729 powerCoefficients10 plusWeights0729 minusWeights0729
    checked0729.1 checked0729.2.1 checked0729.2.2.1 checked0729.2.2.2
    (power_identity10 plusWeights0729) (power_identity10 minusWeights0729) g hg hmax

def envelope0729 : Envelope := ⟨coefficients0729, upper0729, bound0729⟩

def coefficients0730 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (375/262144)]

def upper0730 : ℚ := (3/20971520000000)

def plusWeights0730 : Fin 11 → ℚ := ![(3/20971520000000), (3/2097152000000), (27/4194304000000), (9/524288000000), (63/2097152000000), (189/5242880000000), (63/2097152000000), (9/524288000000), (27/4194304000000), (3/2097152000000), (3/10485760000000)]

def minusWeights0730 : Fin 11 → ℚ := ![(3/20971520000000), (3/2097152000000), (27/4194304000000), (9/524288000000), (63/2097152000000), (189/5242880000000), (63/2097152000000), (9/524288000000), (27/4194304000000), (3/2097152000000), 0]

theorem checked0730 :
    (∀ i, 0 ≤ plusWeights0730 i) ∧
    (∀ i, 0 ≤ minusWeights0730 i) ∧
    (∀ i, plusCoefficients coefficients0730 upper0730 i = powerCoefficients10 plusWeights0730 i) ∧
    (∀ i, minusCoefficients coefficients0730 upper0730 i = powerCoefficients10 minusWeights0730 i) := by
  decide +kernel

theorem bound0730 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0730 g| ≤ (upper0730 : ℝ) :=
  abs_of_coefficients coefficients0730 upper0730 powerCoefficients10 plusWeights0730 minusWeights0730
    checked0730.1 checked0730.2.1 checked0730.2.2.1 checked0730.2.2.2
    (power_identity10 plusWeights0730) (power_identity10 minusWeights0730) g hg hmax

def envelope0730 : Envelope := ⟨coefficients0730, upper0730, bound0730⟩

def coefficients0731 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1125/262144)]

def upper0731 : ℚ := (9/20971520000000)

def plusWeights0731 : Fin 11 → ℚ := ![(9/20971520000000), (9/2097152000000), (81/4194304000000), (27/524288000000), (189/2097152000000), (567/5242880000000), (189/2097152000000), (27/524288000000), (81/4194304000000), (9/2097152000000), (9/10485760000000)]

def minusWeights0731 : Fin 11 → ℚ := ![(9/20971520000000), (9/2097152000000), (81/4194304000000), (27/524288000000), (189/2097152000000), (567/5242880000000), (189/2097152000000), (27/524288000000), (81/4194304000000), (9/2097152000000), 0]

theorem checked0731 :
    (∀ i, 0 ≤ plusWeights0731 i) ∧
    (∀ i, 0 ≤ minusWeights0731 i) ∧
    (∀ i, plusCoefficients coefficients0731 upper0731 i = powerCoefficients10 plusWeights0731 i) ∧
    (∀ i, minusCoefficients coefficients0731 upper0731 i = powerCoefficients10 minusWeights0731 i) := by
  decide +kernel

theorem bound0731 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0731 g| ≤ (upper0731 : ℝ) :=
  abs_of_coefficients coefficients0731 upper0731 powerCoefficients10 plusWeights0731 minusWeights0731
    checked0731.1 checked0731.2.1 checked0731.2.2.1 checked0731.2.2.2
    (power_identity10 plusWeights0731) (power_identity10 minusWeights0731) g hg hmax

def envelope0731 : Envelope := ⟨coefficients0731, upper0731, bound0731⟩

def coefficients0732 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1875/262144)]

def upper0732 : ℚ := (3/4194304000000)

def plusWeights0732 : Fin 11 → ℚ := ![(3/4194304000000), (3/419430400000), (27/838860800000), (9/104857600000), (63/419430400000), (189/1048576000000), (63/419430400000), (9/104857600000), (27/838860800000), (3/419430400000), (3/2097152000000)]

def minusWeights0732 : Fin 11 → ℚ := ![(3/4194304000000), (3/419430400000), (27/838860800000), (9/104857600000), (63/419430400000), (189/1048576000000), (63/419430400000), (9/104857600000), (27/838860800000), (3/419430400000), 0]

theorem checked0732 :
    (∀ i, 0 ≤ plusWeights0732 i) ∧
    (∀ i, 0 ≤ minusWeights0732 i) ∧
    (∀ i, plusCoefficients coefficients0732 upper0732 i = powerCoefficients10 plusWeights0732 i) ∧
    (∀ i, minusCoefficients coefficients0732 upper0732 i = powerCoefficients10 minusWeights0732 i) := by
  decide +kernel

theorem bound0732 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0732 g| ≤ (upper0732 : ℝ) :=
  abs_of_coefficients coefficients0732 upper0732 powerCoefficients10 plusWeights0732 minusWeights0732
    checked0732.1 checked0732.2.1 checked0732.2.2.1 checked0732.2.2.2
    (power_identity10 plusWeights0732) (power_identity10 minusWeights0732) g hg hmax

def envelope0732 : Envelope := ⟨coefficients0732, upper0732, bound0732⟩

def coefficients0733 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (375/32768)]

def upper0733 : ℚ := (3/2621440000000)

def plusWeights0733 : Fin 11 → ℚ := ![(3/2621440000000), (3/262144000000), (27/524288000000), (9/65536000000), (63/262144000000), (189/655360000000), (63/262144000000), (9/65536000000), (27/524288000000), (3/262144000000), (3/1310720000000)]

def minusWeights0733 : Fin 11 → ℚ := ![(3/2621440000000), (3/262144000000), (27/524288000000), (9/65536000000), (63/262144000000), (189/655360000000), (63/262144000000), (9/65536000000), (27/524288000000), (3/262144000000), 0]

theorem checked0733 :
    (∀ i, 0 ≤ plusWeights0733 i) ∧
    (∀ i, 0 ≤ minusWeights0733 i) ∧
    (∀ i, plusCoefficients coefficients0733 upper0733 i = powerCoefficients10 plusWeights0733 i) ∧
    (∀ i, minusCoefficients coefficients0733 upper0733 i = powerCoefficients10 minusWeights0733 i) := by
  decide +kernel

theorem bound0733 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0733 g| ≤ (upper0733 : ℝ) :=
  abs_of_coefficients coefficients0733 upper0733 powerCoefficients10 plusWeights0733 minusWeights0733
    checked0733.1 checked0733.2.1 checked0733.2.2.1 checked0733.2.2.2
    (power_identity10 plusWeights0733) (power_identity10 minusWeights0733) g hg hmax

def envelope0733 : Envelope := ⟨coefficients0733, upper0733, bound0733⟩

def coefficients0734 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (3375/262144)]

def upper0734 : ℚ := (27/20971520000000)

def plusWeights0734 : Fin 11 → ℚ := ![(27/20971520000000), (27/2097152000000), (243/4194304000000), (81/524288000000), (567/2097152000000), (1701/5242880000000), (567/2097152000000), (81/524288000000), (243/4194304000000), (27/2097152000000), (27/10485760000000)]

def minusWeights0734 : Fin 11 → ℚ := ![(27/20971520000000), (27/2097152000000), (243/4194304000000), (81/524288000000), (567/2097152000000), (1701/5242880000000), (567/2097152000000), (81/524288000000), (243/4194304000000), (27/2097152000000), 0]

theorem checked0734 :
    (∀ i, 0 ≤ plusWeights0734 i) ∧
    (∀ i, 0 ≤ minusWeights0734 i) ∧
    (∀ i, plusCoefficients coefficients0734 upper0734 i = powerCoefficients10 plusWeights0734 i) ∧
    (∀ i, minusCoefficients coefficients0734 upper0734 i = powerCoefficients10 minusWeights0734 i) := by
  decide +kernel

theorem bound0734 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0734 g| ≤ (upper0734 : ℝ) :=
  abs_of_coefficients coefficients0734 upper0734 powerCoefficients10 plusWeights0734 minusWeights0734
    checked0734.1 checked0734.2.1 checked0734.2.2.1 checked0734.2.2.2
    (power_identity10 plusWeights0734) (power_identity10 minusWeights0734) g hg hmax

def envelope0734 : Envelope := ⟨coefficients0734, upper0734, bound0734⟩

def coefficients0735 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (4125/262144)]

def upper0735 : ℚ := (33/20971520000000)

def plusWeights0735 : Fin 11 → ℚ := ![(33/20971520000000), (33/2097152000000), (297/4194304000000), (99/524288000000), (693/2097152000000), (2079/5242880000000), (693/2097152000000), (99/524288000000), (297/4194304000000), (33/2097152000000), (33/10485760000000)]

def minusWeights0735 : Fin 11 → ℚ := ![(33/20971520000000), (33/2097152000000), (297/4194304000000), (99/524288000000), (693/2097152000000), (2079/5242880000000), (693/2097152000000), (99/524288000000), (297/4194304000000), (33/2097152000000), 0]

theorem checked0735 :
    (∀ i, 0 ≤ plusWeights0735 i) ∧
    (∀ i, 0 ≤ minusWeights0735 i) ∧
    (∀ i, plusCoefficients coefficients0735 upper0735 i = powerCoefficients10 plusWeights0735 i) ∧
    (∀ i, minusCoefficients coefficients0735 upper0735 i = powerCoefficients10 minusWeights0735 i) := by
  decide +kernel

theorem bound0735 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0735 g| ≤ (upper0735 : ℝ) :=
  abs_of_coefficients coefficients0735 upper0735 powerCoefficients10 plusWeights0735 minusWeights0735
    checked0735.1 checked0735.2.1 checked0735.2.2.1 checked0735.2.2.2
    (power_identity10 plusWeights0735) (power_identity10 minusWeights0735) g hg hmax

def envelope0735 : Envelope := ⟨coefficients0735, upper0735, bound0735⟩

end BilayerDressed.CubicQuarticEnvelopes

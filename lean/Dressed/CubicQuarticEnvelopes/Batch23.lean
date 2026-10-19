import Dressed.CubicQuarticCoefficientBernstein

/-! Explicit scalar polynomial envelopes, not graph/coefficient identification.
Generated from frozen rational data; every sign and basis coefficient is checked
by the Lean kernel. No oracle, sampling, or floating-point premise is used. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def coefficients0736 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (375/16384)]

def upper0736 : ℚ := (3/1310720000000)

def plusWeights0736 : Fin 11 → ℚ := ![(3/1310720000000), (3/131072000000), (27/262144000000), (9/32768000000), (63/131072000000), (189/327680000000), (63/131072000000), (9/32768000000), (27/262144000000), (3/131072000000), (3/655360000000)]

def minusWeights0736 : Fin 11 → ℚ := ![(3/1310720000000), (3/131072000000), (27/262144000000), (9/32768000000), (63/131072000000), (189/327680000000), (63/131072000000), (9/32768000000), (27/262144000000), (3/131072000000), 0]

theorem checked0736 :
    (∀ i, 0 ≤ plusWeights0736 i) ∧
    (∀ i, 0 ≤ minusWeights0736 i) ∧
    (∀ i, plusCoefficients coefficients0736 upper0736 i = powerCoefficients10 plusWeights0736 i) ∧
    (∀ i, minusCoefficients coefficients0736 upper0736 i = powerCoefficients10 minusWeights0736 i) := by
  decide +kernel

theorem bound0736 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0736 g| ≤ (upper0736 : ℝ) :=
  abs_of_coefficients coefficients0736 upper0736 powerCoefficients10 plusWeights0736 minusWeights0736
    checked0736.1 checked0736.2.1 checked0736.2.2.1 checked0736.2.2.2
    (power_identity10 plusWeights0736) (power_identity10 minusWeights0736) g hg hmax

def envelope0736 : Envelope := ⟨coefficients0736, upper0736, bound0736⟩

def coefficients0737 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (25/32768), (25/65536), (125/524288)]

def upper0737 : ℚ := (337/41943040000000)

def plusWeights0737 : Fin 11 → ℚ := ![(337/41943040000000), (337/4194304000000), (3033/8388608000000), (1011/1048576000000), (7077/4194304000000), (21231/10485760000000), (7077/4194304000000), (1011/1048576000000), (3097/8388608000000), (2013/20971520000000), (337/20971520000000)]

def minusWeights0737 : Fin 11 → ℚ := ![(337/41943040000000), (337/4194304000000), (3033/8388608000000), (1011/1048576000000), (7077/4194304000000), (21231/10485760000000), (7077/4194304000000), (1011/1048576000000), (2969/8388608000000), (1357/20971520000000), 0]

theorem checked0737 :
    (∀ i, 0 ≤ plusWeights0737 i) ∧
    (∀ i, 0 ≤ minusWeights0737 i) ∧
    (∀ i, plusCoefficients coefficients0737 upper0737 i = powerCoefficients10 plusWeights0737 i) ∧
    (∀ i, minusCoefficients coefficients0737 upper0737 i = powerCoefficients10 minusWeights0737 i) := by
  decide +kernel

theorem bound0737 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0737 g| ≤ (upper0737 : ℝ) :=
  abs_of_coefficients coefficients0737 upper0737 powerCoefficients10 plusWeights0737 minusWeights0737
    checked0737.1 checked0737.2.1 checked0737.2.2.1 checked0737.2.2.2
    (power_identity10 plusWeights0737) (power_identity10 minusWeights0737) g hg hmax

def envelope0737 : Envelope := ⟨coefficients0737, upper0737, bound0737⟩

def coefficients0738 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (5/4096), (5/4096), (5/16384)]

def upper0738 : ℚ := (441/32768000000000)

def plusWeights0738 : Fin 11 → ℚ := ![(441/32768000000000), (441/3276800000000), (3969/6553600000000), (1323/819200000000), (9261/3276800000000), (27783/8192000000000), (9261/3276800000000), (1323/819200000000), (4049/6553600000000), (21/131072000000), (441/16384000000000)]

def minusWeights0738 : Fin 11 → ℚ := ![(441/32768000000000), (441/3276800000000), (3969/6553600000000), (1323/819200000000), (9261/3276800000000), (27783/8192000000000), (9261/3276800000000), (1323/819200000000), (3889/6553600000000), (357/3276800000000), 0]

theorem checked0738 :
    (∀ i, 0 ≤ plusWeights0738 i) ∧
    (∀ i, 0 ≤ minusWeights0738 i) ∧
    (∀ i, plusCoefficients coefficients0738 upper0738 i = powerCoefficients10 plusWeights0738 i) ∧
    (∀ i, minusCoefficients coefficients0738 upper0738 i = powerCoefficients10 minusWeights0738 i) := by
  decide +kernel

theorem bound0738 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0738 g| ≤ (upper0738 : ℝ) :=
  abs_of_coefficients coefficients0738 upper0738 powerCoefficients10 plusWeights0738 minusWeights0738
    checked0738.1 checked0738.2.1 checked0738.2.2.1 checked0738.2.2.2
    (power_identity10 plusWeights0738) (power_identity10 minusWeights0738) g hg hmax

def envelope0738 : Envelope := ⟨coefficients0738, upper0738, bound0738⟩

def coefficients0739 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (45/32768), (65/65536), (135/65536)]

def upper0739 : ℚ := (1957/131072000000000)

def plusWeights0739 : Fin 11 → ℚ := ![(1957/131072000000000), (1957/13107200000000), (17613/26214400000000), (5871/3276800000000), (41097/13107200000000), (123291/32768000000000), (41097/13107200000000), (5871/3276800000000), (17973/26214400000000), (233/1310720000000), (1957/65536000000000)]

def minusWeights0739 : Fin 11 → ℚ := ![(1957/131072000000000), (1957/13107200000000), (17613/26214400000000), (5871/3276800000000), (41097/13107200000000), (123291/32768000000000), (41097/13107200000000), (5871/3276800000000), (17253/26214400000000), (99/819200000000), 0]

theorem checked0739 :
    (∀ i, 0 ≤ plusWeights0739 i) ∧
    (∀ i, 0 ≤ minusWeights0739 i) ∧
    (∀ i, plusCoefficients coefficients0739 upper0739 i = powerCoefficients10 plusWeights0739 i) ∧
    (∀ i, minusCoefficients coefficients0739 upper0739 i = powerCoefficients10 minusWeights0739 i) := by
  decide +kernel

theorem bound0739 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0739 g| ≤ (upper0739 : ℝ) :=
  abs_of_coefficients coefficients0739 upper0739 powerCoefficients10 plusWeights0739 minusWeights0739
    checked0739.1 checked0739.2.1 checked0739.2.2.1 checked0739.2.2.2
    (power_identity10 plusWeights0739) (power_identity10 minusWeights0739) g hg hmax

def envelope0739 : Envelope := ⟨coefficients0739, upper0739, bound0739⟩

def coefficients0740 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (25/16384), (25/32768), (125/262144)]

def upper0740 : ℚ := (337/20971520000000)

def plusWeights0740 : Fin 11 → ℚ := ![(337/20971520000000), (337/2097152000000), (3033/4194304000000), (1011/524288000000), (7077/2097152000000), (21231/5242880000000), (7077/2097152000000), (1011/524288000000), (3097/4194304000000), (2013/10485760000000), (337/10485760000000)]

def minusWeights0740 : Fin 11 → ℚ := ![(337/20971520000000), (337/2097152000000), (3033/4194304000000), (1011/524288000000), (7077/2097152000000), (21231/5242880000000), (7077/2097152000000), (1011/524288000000), (2969/4194304000000), (1357/10485760000000), 0]

theorem checked0740 :
    (∀ i, 0 ≤ plusWeights0740 i) ∧
    (∀ i, 0 ≤ minusWeights0740 i) ∧
    (∀ i, plusCoefficients coefficients0740 upper0740 i = powerCoefficients10 plusWeights0740 i) ∧
    (∀ i, minusCoefficients coefficients0740 upper0740 i = powerCoefficients10 minusWeights0740 i) := by
  decide +kernel

theorem bound0740 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0740 g| ≤ (upper0740 : ℝ) :=
  abs_of_coefficients coefficients0740 upper0740 powerCoefficients10 plusWeights0740 minusWeights0740
    checked0740.1 checked0740.2.1 checked0740.2.2.1 checked0740.2.2.2
    (power_identity10 plusWeights0740) (power_identity10 minusWeights0740) g hg hmax

def envelope0740 : Envelope := ⟨coefficients0740, upper0740, bound0740⟩

def coefficients0741 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/32768), (75/65536), (375/524288)]

def upper0741 : ℚ := (1011/41943040000000)

def plusWeights0741 : Fin 11 → ℚ := ![(1011/41943040000000), (1011/4194304000000), (9099/8388608000000), (3033/1048576000000), (21231/4194304000000), (63693/10485760000000), (21231/4194304000000), (3033/1048576000000), (9291/8388608000000), (6039/20971520000000), (1011/20971520000000)]

def minusWeights0741 : Fin 11 → ℚ := ![(1011/41943040000000), (1011/4194304000000), (9099/8388608000000), (3033/1048576000000), (21231/4194304000000), (63693/10485760000000), (21231/4194304000000), (3033/1048576000000), (8907/8388608000000), (4071/20971520000000), 0]

theorem checked0741 :
    (∀ i, 0 ≤ plusWeights0741 i) ∧
    (∀ i, 0 ≤ minusWeights0741 i) ∧
    (∀ i, plusCoefficients coefficients0741 upper0741 i = powerCoefficients10 plusWeights0741 i) ∧
    (∀ i, minusCoefficients coefficients0741 upper0741 i = powerCoefficients10 minusWeights0741 i) := by
  decide +kernel

theorem bound0741 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0741 g| ≤ (upper0741 : ℝ) :=
  abs_of_coefficients coefficients0741 upper0741 powerCoefficients10 plusWeights0741 minusWeights0741
    checked0741.1 checked0741.2.1 checked0741.2.2.1 checked0741.2.2.2
    (power_identity10 plusWeights0741) (power_identity10 minusWeights0741) g hg hmax

def envelope0741 : Envelope := ⟨coefficients0741, upper0741, bound0741⟩

def coefficients0742 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/32768), (75/65536), (3375/524288)]

def upper0742 : ℚ := (207/8388608000000)

def plusWeights0742 : Fin 11 → ℚ := ![(207/8388608000000), (207/838860800000), (1863/1677721600000), (621/209715200000), (4347/838860800000), (13041/2097152000000), (4347/838860800000), (621/209715200000), (9507/8388608000000), (6159/20971520000000), (207/4194304000000)]

def minusWeights0742 : Fin 11 → ℚ := ![(207/8388608000000), (207/838860800000), (1863/1677721600000), (621/209715200000), (4347/838860800000), (13041/2097152000000), (4347/838860800000), (621/209715200000), (9123/8388608000000), (4191/20971520000000), 0]

theorem checked0742 :
    (∀ i, 0 ≤ plusWeights0742 i) ∧
    (∀ i, 0 ≤ minusWeights0742 i) ∧
    (∀ i, plusCoefficients coefficients0742 upper0742 i = powerCoefficients10 plusWeights0742 i) ∧
    (∀ i, minusCoefficients coefficients0742 upper0742 i = powerCoefficients10 minusWeights0742 i) := by
  decide +kernel

theorem bound0742 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0742 g| ≤ (upper0742 : ℝ) :=
  abs_of_coefficients coefficients0742 upper0742 powerCoefficients10 plusWeights0742 minusWeights0742
    checked0742.1 checked0742.2.1 checked0742.2.2.1 checked0742.2.2.2
    (power_identity10 plusWeights0742) (power_identity10 minusWeights0742) g hg hmax

def envelope0742 : Envelope := ⟨coefficients0742, upper0742, bound0742⟩

def coefficients0743 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/32768), (75/65536), (8625/524288)]

def upper0743 : ℚ := (1077/41943040000000)

def plusWeights0743 : Fin 11 → ℚ := ![(1077/41943040000000), (1077/4194304000000), (9693/8388608000000), (3231/1048576000000), (22617/4194304000000), (67851/10485760000000), (22617/4194304000000), (3231/1048576000000), (1977/1677721600000), (6369/20971520000000), (1077/20971520000000)]

def minusWeights0743 : Fin 11 → ℚ := ![(1077/41943040000000), (1077/4194304000000), (9693/8388608000000), (3231/1048576000000), (22617/4194304000000), (67851/10485760000000), (22617/4194304000000), (3231/1048576000000), (9501/8388608000000), (4401/20971520000000), 0]

theorem checked0743 :
    (∀ i, 0 ≤ plusWeights0743 i) ∧
    (∀ i, 0 ≤ minusWeights0743 i) ∧
    (∀ i, plusCoefficients coefficients0743 upper0743 i = powerCoefficients10 plusWeights0743 i) ∧
    (∀ i, minusCoefficients coefficients0743 upper0743 i = powerCoefficients10 minusWeights0743 i) := by
  decide +kernel

theorem bound0743 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0743 g| ≤ (upper0743 : ℝ) :=
  abs_of_coefficients coefficients0743 upper0743 powerCoefficients10 plusWeights0743 minusWeights0743
    checked0743.1 checked0743.2.1 checked0743.2.2.1 checked0743.2.2.2
    (power_identity10 plusWeights0743) (power_identity10 minusWeights0743) g hg hmax

def envelope0743 : Envelope := ⟨coefficients0743, upper0743, bound0743⟩

def coefficients0744 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (45/16384), (65/32768), (145/65536)]

def upper0744 : ℚ := (3889/131072000000000)

def plusWeights0744 : Fin 11 → ℚ := ![(3889/131072000000000), (3889/13107200000000), (35001/26214400000000), (11667/3276800000000), (81669/13107200000000), (245007/32768000000000), (81669/13107200000000), (11667/3276800000000), (35721/26214400000000), (927/2621440000000), (3889/65536000000000)]

def minusWeights0744 : Fin 11 → ℚ := ![(3889/131072000000000), (3889/13107200000000), (35001/26214400000000), (11667/3276800000000), (81669/13107200000000), (245007/32768000000000), (81669/13107200000000), (11667/3276800000000), (34281/26214400000000), (3143/13107200000000), 0]

theorem checked0744 :
    (∀ i, 0 ≤ plusWeights0744 i) ∧
    (∀ i, 0 ≤ minusWeights0744 i) ∧
    (∀ i, plusCoefficients coefficients0744 upper0744 i = powerCoefficients10 plusWeights0744 i) ∧
    (∀ i, minusCoefficients coefficients0744 upper0744 i = powerCoefficients10 minusWeights0744 i) := by
  decide +kernel

theorem bound0744 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0744 g| ≤ (upper0744 : ℝ) :=
  abs_of_coefficients coefficients0744 upper0744 powerCoefficients10 plusWeights0744 minusWeights0744
    checked0744.1 checked0744.2.1 checked0744.2.2.1 checked0744.2.2.2
    (power_identity10 plusWeights0744) (power_identity10 minusWeights0744) g hg hmax

def envelope0744 : Envelope := ⟨coefficients0744, upper0744, bound0744⟩

def coefficients0745 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (25/8192), (25/16384), (125/131072)]

def upper0745 : ℚ := (337/10485760000000)

def plusWeights0745 : Fin 11 → ℚ := ![(337/10485760000000), (337/1048576000000), (3033/2097152000000), (1011/262144000000), (7077/1048576000000), (21231/2621440000000), (7077/1048576000000), (1011/262144000000), (3097/2097152000000), (2013/5242880000000), (337/5242880000000)]

def minusWeights0745 : Fin 11 → ℚ := ![(337/10485760000000), (337/1048576000000), (3033/2097152000000), (1011/262144000000), (7077/1048576000000), (21231/2621440000000), (7077/1048576000000), (1011/262144000000), (2969/2097152000000), (1357/5242880000000), 0]

theorem checked0745 :
    (∀ i, 0 ≤ plusWeights0745 i) ∧
    (∀ i, 0 ≤ minusWeights0745 i) ∧
    (∀ i, plusCoefficients coefficients0745 upper0745 i = powerCoefficients10 plusWeights0745 i) ∧
    (∀ i, minusCoefficients coefficients0745 upper0745 i = powerCoefficients10 minusWeights0745 i) := by
  decide +kernel

theorem bound0745 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0745 g| ≤ (upper0745 : ℝ) :=
  abs_of_coefficients coefficients0745 upper0745 powerCoefficients10 plusWeights0745 minusWeights0745
    checked0745.1 checked0745.2.1 checked0745.2.2.1 checked0745.2.2.2
    (power_identity10 plusWeights0745) (power_identity10 minusWeights0745) g hg hmax

def envelope0745 : Envelope := ⟨coefficients0745, upper0745, bound0745⟩

def coefficients0746 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (25/8192), (25/16384), (125/32768)]

def upper0746 : ℚ := (17/524288000000)

def plusWeights0746 : Fin 11 → ℚ := ![(17/524288000000), (17/52428800000), (153/104857600000), (51/13107200000), (357/52428800000), (1071/131072000000), (357/52428800000), (51/13107200000), (781/524288000000), (507/1310720000000), (17/262144000000)]

def minusWeights0746 : Fin 11 → ℚ := ![(17/524288000000), (17/52428800000), (153/104857600000), (51/13107200000), (357/52428800000), (1071/131072000000), (357/52428800000), (51/13107200000), (749/524288000000), (343/1310720000000), 0]

theorem checked0746 :
    (∀ i, 0 ≤ plusWeights0746 i) ∧
    (∀ i, 0 ≤ minusWeights0746 i) ∧
    (∀ i, plusCoefficients coefficients0746 upper0746 i = powerCoefficients10 plusWeights0746 i) ∧
    (∀ i, minusCoefficients coefficients0746 upper0746 i = powerCoefficients10 minusWeights0746 i) := by
  decide +kernel

theorem bound0746 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0746 g| ≤ (upper0746 : ℝ) :=
  abs_of_coefficients coefficients0746 upper0746 powerCoefficients10 plusWeights0746 minusWeights0746
    checked0746.1 checked0746.2.1 checked0746.2.2.1 checked0746.2.2.2
    (power_identity10 plusWeights0746) (power_identity10 minusWeights0746) g hg hmax

def envelope0746 : Envelope := ⟨coefficients0746, upper0746, bound0746⟩

def coefficients0747 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/32768), (195/65536), (405/65536)]

def upper0747 : ℚ := (5871/131072000000000)

def plusWeights0747 : Fin 11 → ℚ := ![(5871/131072000000000), (5871/13107200000000), (52839/26214400000000), (17613/3276800000000), (123291/13107200000000), (369873/32768000000000), (123291/13107200000000), (17613/3276800000000), (53919/26214400000000), (699/1310720000000), (5871/65536000000000)]

def minusWeights0747 : Fin 11 → ℚ := ![(5871/131072000000000), (5871/13107200000000), (52839/26214400000000), (17613/3276800000000), (123291/13107200000000), (369873/32768000000000), (123291/13107200000000), (17613/3276800000000), (51759/26214400000000), (297/819200000000), 0]

theorem checked0747 :
    (∀ i, 0 ≤ plusWeights0747 i) ∧
    (∀ i, 0 ≤ minusWeights0747 i) ∧
    (∀ i, plusCoefficients coefficients0747 upper0747 i = powerCoefficients10 plusWeights0747 i) ∧
    (∀ i, minusCoefficients coefficients0747 upper0747 i = powerCoefficients10 minusWeights0747 i) := by
  decide +kernel

theorem bound0747 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0747 g| ≤ (upper0747 : ℝ) :=
  abs_of_coefficients coefficients0747 upper0747 powerCoefficients10 plusWeights0747 minusWeights0747
    checked0747.1 checked0747.2.1 checked0747.2.2.1 checked0747.2.2.2
    (power_identity10 plusWeights0747) (power_identity10 minusWeights0747) g hg hmax

def envelope0747 : Envelope := ⟨coefficients0747, upper0747, bound0747⟩

def coefficients0748 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/32768), (195/65536), (1995/262144)]

def upper0748 : ℚ := (23559/524288000000000)

def plusWeights0748 : Fin 11 → ℚ := ![(23559/524288000000000), (23559/52428800000000), (212031/104857600000000), (70677/13107200000000), (494739/52428800000000), (1484217/131072000000000), (494739/52428800000000), (70677/13107200000000), (216351/104857600000000), (5607/10485760000000), (23559/262144000000000)]

def minusWeights0748 : Fin 11 → ℚ := ![(23559/524288000000000), (23559/52428800000000), (212031/104857600000000), (70677/13107200000000), (494739/52428800000000), (1484217/131072000000000), (494739/52428800000000), (70677/13107200000000), (207711/104857600000000), (19083/52428800000000), 0]

theorem checked0748 :
    (∀ i, 0 ≤ plusWeights0748 i) ∧
    (∀ i, 0 ≤ minusWeights0748 i) ∧
    (∀ i, plusCoefficients coefficients0748 upper0748 i = powerCoefficients10 plusWeights0748 i) ∧
    (∀ i, minusCoefficients coefficients0748 upper0748 i = powerCoefficients10 minusWeights0748 i) := by
  decide +kernel

theorem bound0748 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0748 g| ≤ (upper0748 : ℝ) :=
  abs_of_coefficients coefficients0748 upper0748 powerCoefficients10 plusWeights0748 minusWeights0748
    checked0748.1 checked0748.2.1 checked0748.2.2.1 checked0748.2.2.2
    (power_identity10 plusWeights0748) (power_identity10 minusWeights0748) g hg hmax

def envelope0748 : Envelope := ⟨coefficients0748, upper0748, bound0748⟩

def coefficients0749 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/32768), (195/65536), (1935/131072)]

def upper0749 : ℚ := (11967/262144000000000)

def plusWeights0749 : Fin 11 → ℚ := ![(11967/262144000000000), (11967/26214400000000), (107703/52428800000000), (35901/6553600000000), (251307/26214400000000), (753921/65536000000000), (251307/26214400000000), (35901/6553600000000), (109863/52428800000000), (2841/5242880000000), (11967/131072000000000)]

def minusWeights0749 : Fin 11 → ℚ := ![(11967/262144000000000), (11967/26214400000000), (107703/52428800000000), (35901/6553600000000), (251307/26214400000000), (753921/65536000000000), (251307/26214400000000), (35901/6553600000000), (105543/52428800000000), (9729/26214400000000), 0]

theorem checked0749 :
    (∀ i, 0 ≤ plusWeights0749 i) ∧
    (∀ i, 0 ≤ minusWeights0749 i) ∧
    (∀ i, plusCoefficients coefficients0749 upper0749 i = powerCoefficients10 plusWeights0749 i) ∧
    (∀ i, minusCoefficients coefficients0749 upper0749 i = powerCoefficients10 minusWeights0749 i) := by
  decide +kernel

theorem bound0749 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0749 g| ≤ (upper0749 : ℝ) :=
  abs_of_coefficients coefficients0749 upper0749 powerCoefficients10 plusWeights0749 minusWeights0749
    checked0749.1 checked0749.2.1 checked0749.2.2.1 checked0749.2.2.2
    (power_identity10 plusWeights0749) (power_identity10 minusWeights0749) g hg hmax

def envelope0749 : Envelope := ⟨coefficients0749, upper0749, bound0749⟩

def coefficients0750 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/16384), (75/32768), (375/262144)]

def upper0750 : ℚ := (1011/20971520000000)

def plusWeights0750 : Fin 11 → ℚ := ![(1011/20971520000000), (1011/2097152000000), (9099/4194304000000), (3033/524288000000), (21231/2097152000000), (63693/5242880000000), (21231/2097152000000), (3033/524288000000), (9291/4194304000000), (6039/10485760000000), (1011/10485760000000)]

def minusWeights0750 : Fin 11 → ℚ := ![(1011/20971520000000), (1011/2097152000000), (9099/4194304000000), (3033/524288000000), (21231/2097152000000), (63693/5242880000000), (21231/2097152000000), (3033/524288000000), (8907/4194304000000), (4071/10485760000000), 0]

theorem checked0750 :
    (∀ i, 0 ≤ plusWeights0750 i) ∧
    (∀ i, 0 ≤ minusWeights0750 i) ∧
    (∀ i, plusCoefficients coefficients0750 upper0750 i = powerCoefficients10 plusWeights0750 i) ∧
    (∀ i, minusCoefficients coefficients0750 upper0750 i = powerCoefficients10 minusWeights0750 i) := by
  decide +kernel

theorem bound0750 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0750 g| ≤ (upper0750 : ℝ) :=
  abs_of_coefficients coefficients0750 upper0750 powerCoefficients10 plusWeights0750 minusWeights0750
    checked0750.1 checked0750.2.1 checked0750.2.2.1 checked0750.2.2.2
    (power_identity10 plusWeights0750) (power_identity10 minusWeights0750) g hg hmax

def envelope0750 : Envelope := ⟨coefficients0750, upper0750, bound0750⟩

def coefficients0751 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/16384), (75/32768), (1125/262144)]

def upper0751 : ℚ := (1017/20971520000000)

def plusWeights0751 : Fin 11 → ℚ := ![(1017/20971520000000), (1017/2097152000000), (9153/4194304000000), (3051/524288000000), (21357/2097152000000), (64071/5242880000000), (21357/2097152000000), (3051/524288000000), (1869/838860800000), (6069/10485760000000), (1017/10485760000000)]

def minusWeights0751 : Fin 11 → ℚ := ![(1017/20971520000000), (1017/2097152000000), (9153/4194304000000), (3051/524288000000), (21357/2097152000000), (64071/5242880000000), (21357/2097152000000), (3051/524288000000), (8961/4194304000000), (4101/10485760000000), 0]

theorem checked0751 :
    (∀ i, 0 ≤ plusWeights0751 i) ∧
    (∀ i, 0 ≤ minusWeights0751 i) ∧
    (∀ i, plusCoefficients coefficients0751 upper0751 i = powerCoefficients10 plusWeights0751 i) ∧
    (∀ i, minusCoefficients coefficients0751 upper0751 i = powerCoefficients10 minusWeights0751 i) := by
  decide +kernel

theorem bound0751 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0751 g| ≤ (upper0751 : ℝ) :=
  abs_of_coefficients coefficients0751 upper0751 powerCoefficients10 plusWeights0751 minusWeights0751
    checked0751.1 checked0751.2.1 checked0751.2.2.1 checked0751.2.2.2
    (power_identity10 plusWeights0751) (power_identity10 minusWeights0751) g hg hmax

def envelope0751 : Envelope := ⟨coefficients0751, upper0751, bound0751⟩

def coefficients0752 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/16384), (75/32768), (1875/131072)]

def upper0752 : ℚ := (519/10485760000000)

def plusWeights0752 : Fin 11 → ℚ := ![(519/10485760000000), (519/1048576000000), (4671/2097152000000), (1557/262144000000), (10899/1048576000000), (32697/2621440000000), (10899/1048576000000), (1557/262144000000), (4767/2097152000000), (3087/5242880000000), (519/5242880000000)]

def minusWeights0752 : Fin 11 → ℚ := ![(519/10485760000000), (519/1048576000000), (4671/2097152000000), (1557/262144000000), (10899/1048576000000), (32697/2621440000000), (10899/1048576000000), (1557/262144000000), (183/83886080000), (2103/5242880000000), 0]

theorem checked0752 :
    (∀ i, 0 ≤ plusWeights0752 i) ∧
    (∀ i, 0 ≤ minusWeights0752 i) ∧
    (∀ i, plusCoefficients coefficients0752 upper0752 i = powerCoefficients10 plusWeights0752 i) ∧
    (∀ i, minusCoefficients coefficients0752 upper0752 i = powerCoefficients10 minusWeights0752 i) := by
  decide +kernel

theorem bound0752 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0752 g| ≤ (upper0752 : ℝ) :=
  abs_of_coefficients coefficients0752 upper0752 powerCoefficients10 plusWeights0752 minusWeights0752
    checked0752.1 checked0752.2.1 checked0752.2.2.1 checked0752.2.2.2
    (power_identity10 plusWeights0752) (power_identity10 minusWeights0752) g hg hmax

def envelope0752 : Envelope := ⟨coefficients0752, upper0752, bound0752⟩

def coefficients0753 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (25/4096), (25/8192), (125/65536)]

def upper0753 : ℚ := (337/5242880000000)

def plusWeights0753 : Fin 11 → ℚ := ![(337/5242880000000), (337/524288000000), (3033/1048576000000), (1011/131072000000), (7077/524288000000), (21231/1310720000000), (7077/524288000000), (1011/131072000000), (3097/1048576000000), (2013/2621440000000), (337/2621440000000)]

def minusWeights0753 : Fin 11 → ℚ := ![(337/5242880000000), (337/524288000000), (3033/1048576000000), (1011/131072000000), (7077/524288000000), (21231/1310720000000), (7077/524288000000), (1011/131072000000), (2969/1048576000000), (1357/2621440000000), 0]

theorem checked0753 :
    (∀ i, 0 ≤ plusWeights0753 i) ∧
    (∀ i, 0 ≤ minusWeights0753 i) ∧
    (∀ i, plusCoefficients coefficients0753 upper0753 i = powerCoefficients10 plusWeights0753 i) ∧
    (∀ i, minusCoefficients coefficients0753 upper0753 i = powerCoefficients10 minusWeights0753 i) := by
  decide +kernel

theorem bound0753 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0753 g| ≤ (upper0753 : ℝ) :=
  abs_of_coefficients coefficients0753 upper0753 powerCoefficients10 plusWeights0753 minusWeights0753
    checked0753.1 checked0753.2.1 checked0753.2.2.1 checked0753.2.2.2
    (power_identity10 plusWeights0753) (power_identity10 minusWeights0753) g hg hmax

def envelope0753 : Envelope := ⟨coefficients0753, upper0753, bound0753⟩

def coefficients0754 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (225/32768), (325/65536), (275/32768)]

def upper0754 : ℚ := (61/819200000000)

def plusWeights0754 : Fin 11 → ℚ := ![(61/819200000000), (61/81920000000), (549/163840000000), (183/20480000000), (1281/81920000000), (3843/204800000000), (1281/81920000000), (183/20480000000), (2241/655360000000), (93/104857600000), (61/409600000000)]

def minusWeights0754 : Fin 11 → ℚ := ![(61/819200000000), (61/81920000000), (549/163840000000), (183/20480000000), (1281/81920000000), (3843/204800000000), (1281/81920000000), (183/20480000000), (2151/655360000000), (1579/2621440000000), 0]

theorem checked0754 :
    (∀ i, 0 ≤ plusWeights0754 i) ∧
    (∀ i, 0 ≤ minusWeights0754 i) ∧
    (∀ i, plusCoefficients coefficients0754 upper0754 i = powerCoefficients10 plusWeights0754 i) ∧
    (∀ i, minusCoefficients coefficients0754 upper0754 i = powerCoefficients10 minusWeights0754 i) := by
  decide +kernel

theorem bound0754 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0754 g| ≤ (upper0754 : ℝ) :=
  abs_of_coefficients coefficients0754 upper0754 powerCoefficients10 plusWeights0754 minusWeights0754
    checked0754.1 checked0754.2.1 checked0754.2.2.1 checked0754.2.2.2
    (power_identity10 plusWeights0754) (power_identity10 minusWeights0754) g hg hmax

def envelope0754 : Envelope := ⟨coefficients0754, upper0754, bound0754⟩

def coefficients0755 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/16384), (195/32768), (435/65536)]

def upper0755 : ℚ := (11667/131072000000000)

def plusWeights0755 : Fin 11 → ℚ := ![(11667/131072000000000), (11667/13107200000000), (105003/26214400000000), (35001/3276800000000), (245007/13107200000000), (735021/32768000000000), (245007/13107200000000), (35001/3276800000000), (107163/26214400000000), (2781/2621440000000), (11667/65536000000000)]

def minusWeights0755 : Fin 11 → ℚ := ![(11667/131072000000000), (11667/13107200000000), (105003/26214400000000), (35001/3276800000000), (245007/13107200000000), (735021/32768000000000), (245007/13107200000000), (35001/3276800000000), (102843/26214400000000), (9429/13107200000000), 0]

theorem checked0755 :
    (∀ i, 0 ≤ plusWeights0755 i) ∧
    (∀ i, 0 ≤ minusWeights0755 i) ∧
    (∀ i, plusCoefficients coefficients0755 upper0755 i = powerCoefficients10 plusWeights0755 i) ∧
    (∀ i, minusCoefficients coefficients0755 upper0755 i = powerCoefficients10 minusWeights0755 i) := by
  decide +kernel

theorem bound0755 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0755 g| ≤ (upper0755 : ℝ) :=
  abs_of_coefficients coefficients0755 upper0755 powerCoefficients10 plusWeights0755 minusWeights0755
    checked0755.1 checked0755.2.1 checked0755.2.2.1 checked0755.2.2.2
    (power_identity10 plusWeights0755) (power_identity10 minusWeights0755) g hg hmax

def envelope0755 : Envelope := ⟨coefficients0755, upper0755, bound0755⟩

def coefficients0756 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/16384), (195/32768), (5115/262144)]

def upper0756 : ℚ := (47343/524288000000000)

def plusWeights0756 : Fin 11 → ℚ := ![(47343/524288000000000), (47343/52428800000000), (426087/104857600000000), (142029/13107200000000), (994203/52428800000000), (2982609/131072000000000), (994203/52428800000000), (142029/13107200000000), (434727/104857600000000), (11259/10485760000000), (47343/262144000000000)]

def minusWeights0756 : Fin 11 → ℚ := ![(47343/524288000000000), (47343/52428800000000), (426087/104857600000000), (142029/13107200000000), (994203/52428800000000), (2982609/131072000000000), (994203/52428800000000), (142029/13107200000000), (417447/104857600000000), (38391/52428800000000), 0]

theorem checked0756 :
    (∀ i, 0 ≤ plusWeights0756 i) ∧
    (∀ i, 0 ≤ minusWeights0756 i) ∧
    (∀ i, plusCoefficients coefficients0756 upper0756 i = powerCoefficients10 plusWeights0756 i) ∧
    (∀ i, minusCoefficients coefficients0756 upper0756 i = powerCoefficients10 minusWeights0756 i) := by
  decide +kernel

theorem bound0756 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0756 g| ≤ (upper0756 : ℝ) :=
  abs_of_coefficients coefficients0756 upper0756 powerCoefficients10 plusWeights0756 minusWeights0756
    checked0756.1 checked0756.2.1 checked0756.2.2.1 checked0756.2.2.2
    (power_identity10 plusWeights0756) (power_identity10 minusWeights0756) g hg hmax

def envelope0756 : Envelope := ⟨coefficients0756, upper0756, bound0756⟩

def coefficients0757 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/8192), (75/16384), (1875/262144)]

def upper0757 : ℚ := (2031/20971520000000)

def plusWeights0757 : Fin 11 → ℚ := ![(2031/20971520000000), (2031/2097152000000), (18279/4194304000000), (6093/524288000000), (42651/2097152000000), (127953/5242880000000), (42651/2097152000000), (6093/524288000000), (18663/4194304000000), (12123/10485760000000), (2031/10485760000000)]

def minusWeights0757 : Fin 11 → ℚ := ![(2031/20971520000000), (2031/2097152000000), (18279/4194304000000), (6093/524288000000), (42651/2097152000000), (127953/5242880000000), (42651/2097152000000), (6093/524288000000), (3579/838860800000), (8187/10485760000000), 0]

theorem checked0757 :
    (∀ i, 0 ≤ plusWeights0757 i) ∧
    (∀ i, 0 ≤ minusWeights0757 i) ∧
    (∀ i, plusCoefficients coefficients0757 upper0757 i = powerCoefficients10 plusWeights0757 i) ∧
    (∀ i, minusCoefficients coefficients0757 upper0757 i = powerCoefficients10 minusWeights0757 i) := by
  decide +kernel

theorem bound0757 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0757 g| ≤ (upper0757 : ℝ) :=
  abs_of_coefficients coefficients0757 upper0757 powerCoefficients10 plusWeights0757 minusWeights0757
    checked0757.1 checked0757.2.1 checked0757.2.2.1 checked0757.2.2.2
    (power_identity10 plusWeights0757) (power_identity10 minusWeights0757) g hg hmax

def envelope0757 : Envelope := ⟨coefficients0757, upper0757, bound0757⟩

def coefficients0758 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/8192), (75/16384), (375/32768)]

def upper0758 : ℚ := (51/524288000000)

def plusWeights0758 : Fin 11 → ℚ := ![(51/524288000000), (51/52428800000), (459/104857600000), (153/13107200000), (1071/52428800000), (3213/131072000000), (1071/52428800000), (153/13107200000), (2343/524288000000), (1521/1310720000000), (51/262144000000)]

def minusWeights0758 : Fin 11 → ℚ := ![(51/524288000000), (51/52428800000), (459/104857600000), (153/13107200000), (1071/52428800000), (3213/131072000000), (1071/52428800000), (153/13107200000), (2247/524288000000), (1029/1310720000000), 0]

theorem checked0758 :
    (∀ i, 0 ≤ plusWeights0758 i) ∧
    (∀ i, 0 ≤ minusWeights0758 i) ∧
    (∀ i, plusCoefficients coefficients0758 upper0758 i = powerCoefficients10 plusWeights0758 i) ∧
    (∀ i, minusCoefficients coefficients0758 upper0758 i = powerCoefficients10 minusWeights0758 i) := by
  decide +kernel

theorem bound0758 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0758 g| ≤ (upper0758 : ℝ) :=
  abs_of_coefficients coefficients0758 upper0758 powerCoefficients10 plusWeights0758 minusWeights0758
    checked0758.1 checked0758.2.1 checked0758.2.2.1 checked0758.2.2.2
    (power_identity10 plusWeights0758) (power_identity10 minusWeights0758) g hg hmax

def envelope0758 : Envelope := ⟨coefficients0758, upper0758, bound0758⟩

def coefficients0759 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (75/8192), (75/16384), (4125/262144)]

def upper0759 : ℚ := (2049/20971520000000)

def plusWeights0759 : Fin 11 → ℚ := ![(2049/20971520000000), (2049/2097152000000), (18441/4194304000000), (6147/524288000000), (43029/2097152000000), (129087/5242880000000), (43029/2097152000000), (6147/524288000000), (753/167772160000), (12213/10485760000000), (2049/10485760000000)]

def minusWeights0759 : Fin 11 → ℚ := ![(2049/20971520000000), (2049/2097152000000), (18441/4194304000000), (6147/524288000000), (43029/2097152000000), (129087/5242880000000), (43029/2097152000000), (6147/524288000000), (18057/4194304000000), (8277/10485760000000), 0]

theorem checked0759 :
    (∀ i, 0 ≤ plusWeights0759 i) ∧
    (∀ i, 0 ≤ minusWeights0759 i) ∧
    (∀ i, plusCoefficients coefficients0759 upper0759 i = powerCoefficients10 plusWeights0759 i) ∧
    (∀ i, minusCoefficients coefficients0759 upper0759 i = powerCoefficients10 minusWeights0759 i) := by
  decide +kernel

theorem bound0759 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0759 g| ≤ (upper0759 : ℝ) :=
  abs_of_coefficients coefficients0759 upper0759 powerCoefficients10 plusWeights0759 minusWeights0759
    checked0759.1 checked0759.2.1 checked0759.2.2.1 checked0759.2.2.2
    (power_identity10 plusWeights0759) (power_identity10 minusWeights0759) g hg hmax

def envelope0759 : Envelope := ⟨coefficients0759, upper0759, bound0759⟩

def coefficients0760 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (25/2048), (25/2048), (25/8192)]

def upper0760 : ℚ := (441/3276800000000)

def plusWeights0760 : Fin 11 → ℚ := ![(441/3276800000000), (441/327680000000), (3969/655360000000), (1323/81920000000), (9261/327680000000), (27783/819200000000), (9261/327680000000), (1323/81920000000), (4049/655360000000), (21/13107200000), (441/1638400000000)]

def minusWeights0760 : Fin 11 → ℚ := ![(441/3276800000000), (441/327680000000), (3969/655360000000), (1323/81920000000), (9261/327680000000), (27783/819200000000), (9261/327680000000), (1323/81920000000), (3889/655360000000), (357/327680000000), 0]

theorem checked0760 :
    (∀ i, 0 ≤ plusWeights0760 i) ∧
    (∀ i, 0 ≤ minusWeights0760 i) ∧
    (∀ i, plusCoefficients coefficients0760 upper0760 i = powerCoefficients10 plusWeights0760 i) ∧
    (∀ i, minusCoefficients coefficients0760 upper0760 i = powerCoefficients10 minusWeights0760 i) := by
  decide +kernel

theorem bound0760 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0760 g| ≤ (upper0760 : ℝ) :=
  abs_of_coefficients coefficients0760 upper0760 powerCoefficients10 plusWeights0760 minusWeights0760
    checked0760.1 checked0760.2.1 checked0760.2.2.1 checked0760.2.2.2
    (power_identity10 plusWeights0760) (power_identity10 minusWeights0760) g hg hmax

def envelope0760 : Envelope := ⟨coefficients0760, upper0760, bound0760⟩

def coefficients0761 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (405/32768), (585/65536), (3555/131072)]

def upper0761 : ℚ := (35451/262144000000000)

def plusWeights0761 : Fin 11 → ℚ := ![(35451/262144000000000), (35451/26214400000000), (319059/52428800000000), (106353/6553600000000), (744471/26214400000000), (2233413/65536000000000), (744471/26214400000000), (106353/6553600000000), (325539/52428800000000), (8433/5242880000000), (35451/131072000000000)]

def minusWeights0761 : Fin 11 → ℚ := ![(35451/262144000000000), (35451/26214400000000), (319059/52428800000000), (106353/6553600000000), (744471/26214400000000), (2233413/65536000000000), (744471/26214400000000), (106353/6553600000000), (312579/52428800000000), (28737/26214400000000), 0]

theorem checked0761 :
    (∀ i, 0 ≤ plusWeights0761 i) ∧
    (∀ i, 0 ≤ minusWeights0761 i) ∧
    (∀ i, plusCoefficients coefficients0761 upper0761 i = powerCoefficients10 plusWeights0761 i) ∧
    (∀ i, minusCoefficients coefficients0761 upper0761 i = powerCoefficients10 minusWeights0761 i) := by
  decide +kernel

theorem bound0761 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0761 g| ≤ (upper0761 : ℝ) :=
  abs_of_coefficients coefficients0761 upper0761 powerCoefficients10 plusWeights0761 minusWeights0761
    checked0761.1 checked0761.2.1 checked0761.2.2.1 checked0761.2.2.2
    (power_identity10 plusWeights0761) (power_identity10 minusWeights0761) g hg hmax

def envelope0761 : Envelope := ⟨coefficients0761, upper0761, bound0761⟩

def coefficients0762 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (225/16384), (225/32768), (1125/262144)]

def upper0762 : ℚ := (3033/20971520000000)

def plusWeights0762 : Fin 11 → ℚ := ![(3033/20971520000000), (3033/2097152000000), (27297/4194304000000), (9099/524288000000), (63693/2097152000000), (191079/5242880000000), (63693/2097152000000), (9099/524288000000), (27873/4194304000000), (18117/10485760000000), (3033/10485760000000)]

def minusWeights0762 : Fin 11 → ℚ := ![(3033/20971520000000), (3033/2097152000000), (27297/4194304000000), (9099/524288000000), (63693/2097152000000), (191079/5242880000000), (63693/2097152000000), (9099/524288000000), (26721/4194304000000), (12213/10485760000000), 0]

theorem checked0762 :
    (∀ i, 0 ≤ plusWeights0762 i) ∧
    (∀ i, 0 ≤ minusWeights0762 i) ∧
    (∀ i, plusCoefficients coefficients0762 upper0762 i = powerCoefficients10 plusWeights0762 i) ∧
    (∀ i, minusCoefficients coefficients0762 upper0762 i = powerCoefficients10 minusWeights0762 i) := by
  decide +kernel

theorem bound0762 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0762 g| ≤ (upper0762 : ℝ) :=
  abs_of_coefficients coefficients0762 upper0762 powerCoefficients10 plusWeights0762 minusWeights0762
    checked0762.1 checked0762.2.1 checked0762.2.2.1 checked0762.2.2.2
    (power_identity10 plusWeights0762) (power_identity10 minusWeights0762) g hg hmax

def envelope0762 : Envelope := ⟨coefficients0762, upper0762, bound0762⟩

def coefficients0763 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (225/16384), (225/32768), (1875/262144)]

def upper0763 : ℚ := (3039/20971520000000)

def plusWeights0763 : Fin 11 → ℚ := ![(3039/20971520000000), (3039/2097152000000), (27351/4194304000000), (9117/524288000000), (63819/2097152000000), (191457/5242880000000), (63819/2097152000000), (9117/524288000000), (27927/4194304000000), (18147/10485760000000), (3039/10485760000000)]

def minusWeights0763 : Fin 11 → ℚ := ![(3039/20971520000000), (3039/2097152000000), (27351/4194304000000), (9117/524288000000), (63819/2097152000000), (191457/5242880000000), (63819/2097152000000), (9117/524288000000), (1071/167772160000), (12243/10485760000000), 0]

theorem checked0763 :
    (∀ i, 0 ≤ plusWeights0763 i) ∧
    (∀ i, 0 ≤ minusWeights0763 i) ∧
    (∀ i, plusCoefficients coefficients0763 upper0763 i = powerCoefficients10 plusWeights0763 i) ∧
    (∀ i, minusCoefficients coefficients0763 upper0763 i = powerCoefficients10 minusWeights0763 i) := by
  decide +kernel

theorem bound0763 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0763 g| ≤ (upper0763 : ℝ) :=
  abs_of_coefficients coefficients0763 upper0763 powerCoefficients10 plusWeights0763 minusWeights0763
    checked0763.1 checked0763.2.1 checked0763.2.2.1 checked0763.2.2.2
    (power_identity10 plusWeights0763) (power_identity10 minusWeights0763) g hg hmax

def envelope0763 : Envelope := ⟨coefficients0763, upper0763, bound0763⟩

def coefficients0764 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/8192), (195/16384), (435/32768)]

def upper0764 : ℚ := (11667/65536000000000)

def plusWeights0764 : Fin 11 → ℚ := ![(11667/65536000000000), (11667/6553600000000), (105003/13107200000000), (35001/1638400000000), (245007/6553600000000), (735021/16384000000000), (245007/6553600000000), (35001/1638400000000), (107163/13107200000000), (2781/1310720000000), (11667/32768000000000)]

def minusWeights0764 : Fin 11 → ℚ := ![(11667/65536000000000), (11667/6553600000000), (105003/13107200000000), (35001/1638400000000), (245007/6553600000000), (735021/16384000000000), (245007/6553600000000), (35001/1638400000000), (102843/13107200000000), (9429/6553600000000), 0]

theorem checked0764 :
    (∀ i, 0 ≤ plusWeights0764 i) ∧
    (∀ i, 0 ≤ minusWeights0764 i) ∧
    (∀ i, plusCoefficients coefficients0764 upper0764 i = powerCoefficients10 plusWeights0764 i) ∧
    (∀ i, minusCoefficients coefficients0764 upper0764 i = powerCoefficients10 minusWeights0764 i) := by
  decide +kernel

theorem bound0764 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0764 g| ≤ (upper0764 : ℝ) :=
  abs_of_coefficients coefficients0764 upper0764 powerCoefficients10 plusWeights0764 minusWeights0764
    checked0764.1 checked0764.2.1 checked0764.2.2.1 checked0764.2.2.2
    (power_identity10 plusWeights0764) (power_identity10 minusWeights0764) g hg hmax

def envelope0764 : Envelope := ⟨coefficients0764, upper0764, bound0764⟩

def coefficients0765 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (135/8192), (195/16384), (2865/131072)]

def upper0765 : ℚ := (46893/262144000000000)

def plusWeights0765 : Fin 11 → ℚ := ![(46893/262144000000000), (46893/26214400000000), (422037/52428800000000), (140679/6553600000000), (984753/26214400000000), (2954259/65536000000000), (984753/26214400000000), (140679/6553600000000), (430677/52428800000000), (11169/5242880000000), (46893/131072000000000)]

def minusWeights0765 : Fin 11 → ℚ := ![(46893/262144000000000), (46893/26214400000000), (422037/52428800000000), (140679/6553600000000), (984753/26214400000000), (2954259/65536000000000), (984753/26214400000000), (140679/6553600000000), (413397/52428800000000), (37941/26214400000000), 0]

theorem checked0765 :
    (∀ i, 0 ≤ plusWeights0765 i) ∧
    (∀ i, 0 ≤ minusWeights0765 i) ∧
    (∀ i, plusCoefficients coefficients0765 upper0765 i = powerCoefficients10 plusWeights0765 i) ∧
    (∀ i, minusCoefficients coefficients0765 upper0765 i = powerCoefficients10 minusWeights0765 i) := by
  decide +kernel

theorem bound0765 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0765 g| ≤ (upper0765 : ℝ) :=
  abs_of_coefficients coefficients0765 upper0765 powerCoefficients10 plusWeights0765 minusWeights0765
    checked0765.1 checked0765.2.1 checked0765.2.2.1 checked0765.2.2.2
    (power_identity10 plusWeights0765) (power_identity10 minusWeights0765) g hg hmax

def envelope0765 : Envelope := ⟨coefficients0765, upper0765, bound0765⟩

def coefficients0766 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (555/32768), (735/65536), (5235/262144)]

def upper0766 : ℚ := (95727/524288000000000)

def plusWeights0766 : Fin 11 → ℚ := ![(95727/524288000000000), (95727/52428800000000), (861543/104857600000000), (287181/13107200000000), (2010267/52428800000000), (6030801/131072000000000), (2010267/52428800000000), (287181/13107200000000), (879303/104857600000000), (4563/2097152000000), (95727/262144000000000)]

def minusWeights0766 : Fin 11 → ℚ := ![(95727/524288000000000), (95727/52428800000000), (861543/104857600000000), (287181/13107200000000), (2010267/52428800000000), (6030801/131072000000000), (2010267/52428800000000), (287181/13107200000000), (843783/104857600000000), (77379/52428800000000), 0]

theorem checked0766 :
    (∀ i, 0 ≤ plusWeights0766 i) ∧
    (∀ i, 0 ≤ minusWeights0766 i) ∧
    (∀ i, plusCoefficients coefficients0766 upper0766 i = powerCoefficients10 plusWeights0766 i) ∧
    (∀ i, minusCoefficients coefficients0766 upper0766 i = powerCoefficients10 minusWeights0766 i) := by
  decide +kernel

theorem bound0766 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0766 g| ≤ (upper0766 : ℝ) :=
  abs_of_coefficients coefficients0766 upper0766 powerCoefficients10 plusWeights0766 minusWeights0766
    checked0766.1 checked0766.2.1 checked0766.2.2.1 checked0766.2.2.2
    (power_identity10 plusWeights0766) (power_identity10 minusWeights0766) g hg hmax

def envelope0766 : Envelope := ⟨coefficients0766, upper0766, bound0766⟩

def coefficients0767 : Fin 11 → ℚ := ![0, 0, 0, 0, 0, 0, 0, 0, (35/2048), (35/2048), (35/8192)]

def upper0767 : ℚ := (3087/16384000000000)

def plusWeights0767 : Fin 11 → ℚ := ![(3087/16384000000000), (3087/1638400000000), (27783/3276800000000), (9261/409600000000), (64827/1638400000000), (194481/4096000000000), (64827/1638400000000), (9261/409600000000), (28343/3276800000000), (147/65536000000), (3087/8192000000000)]

def minusWeights0767 : Fin 11 → ℚ := ![(3087/16384000000000), (3087/1638400000000), (27783/3276800000000), (9261/409600000000), (64827/1638400000000), (194481/4096000000000), (64827/1638400000000), (9261/409600000000), (27223/3276800000000), (2499/1638400000000), 0]

theorem checked0767 :
    (∀ i, 0 ≤ plusWeights0767 i) ∧
    (∀ i, 0 ≤ minusWeights0767 i) ∧
    (∀ i, plusCoefficients coefficients0767 upper0767 i = powerCoefficients10 plusWeights0767 i) ∧
    (∀ i, minusCoefficients coefficients0767 upper0767 i = powerCoefficients10 minusWeights0767 i) := by
  decide +kernel

theorem bound0767 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff coefficients0767 g| ≤ (upper0767 : ℝ) :=
  abs_of_coefficients coefficients0767 upper0767 powerCoefficients10 plusWeights0767 minusWeights0767
    checked0767.1 checked0767.2.1 checked0767.2.2.1 checked0767.2.2.2
    (power_identity10 plusWeights0767) (power_identity10 minusWeights0767) g hg hmax

def envelope0767 : Envelope := ⟨coefficients0767, upper0767, bound0767⟩

end BilayerDressed.CubicQuarticEnvelopes

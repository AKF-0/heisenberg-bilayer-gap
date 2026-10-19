import Dressed.QuarticIntegerKernelData
import Dressed.QuarticMeanTransport
import Dressed.CubicSeedSupersolution

/-! Exact interpretation of a finite integer covariance cache.
The finite rational row checks are separate inputs here; the concrete module
proves those checks and discharges them against the three actual graph kernels.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerCovariance
open BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open QuarticIntegerArrays QuarticPhysicalMean
set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

/-- Integer numerator of the absolute cubic kernel at exactly g=1/10. -/
def endpointNumerator (a : KernelCoefficients) : ℤ := |100*a 0+10*a 1+a 2|

/-- Exact rational copy of the already-proved covariance correction. -/
def tauRational (total : ℕ) : ℚ :=
  (493/4000)*(total/64000^2)/(1-(493/4000)^2)

theorem tauRational_cast (total : ℕ) : (tauRational total:ℝ)=tau total := by
  norm_num [tauRational,tau]

theorem tau_nonneg (total : ℕ) : 0 ≤ tau total := by
  unfold tau
  apply div_nonneg
  · exact mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _) (by norm_num))
  · norm_num

/-- Exact endpoint evaluation, not an entrywise upper bound. -/
theorem positiveKernel_endpoint (n m : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (u v : Torus.Vertex n m) :
    positiveKernel n m h (1/10) u v=
      (endpointNumerator (kernel n m u v):ℝ)/64000 := by
  have he := kernel_evaluate n m h hi u v (1/10)
  norm_num [evaluateKernel] at he
  have hk : cubicKernel (graph n m h) (1/10) u v=
      ((100*(kernel n m u v) 0+10*(kernel n m u v) 1+(kernel n m u v) 2:ℤ):ℝ)/64000 := by
    push_cast
    linarith
  unfold positiveKernel
  rw [hk]
  simp [endpointNumerator,abs_div]

variable (n m : ℕ) [NeZero (2*n)] [NeZero (2*m)]

def cachedNumerator (nums : Array ℤ) (u v : Torus.Vertex n m) : ℤ :=
  nums.getD (QuarticRowMajor.index n m (v-u)).val 0

def cachedCovariance (nums : Array ℤ) (den : ℕ) (u v : Torus.Vertex n m) : ℝ :=
  (cachedNumerator n m nums u v:ℝ)/(den:ℝ)

/-- A proved rational row identity and the actual graph kernel cache identify the
entire covariance on arbitrary pairs of sites, not just the origin row. -/
theorem cachedCovariance_eq (nums : Array ℤ) (den total : ℕ)
    (kd : Array KernelCoefficients) (h : Conditions n m) (hi : IncidenceIdentity n m)
    (hk : cachedKernel n m kd=kernel n m)
    (hr : ∀ q : Fin ((2*n)*(2*m)),
      (nums.getD q.val 0:ℚ)/(den:ℚ)=
        (endpointNumerator (kd.getD q.val 0):ℚ)/64000+tauRational total) :
    cachedCovariance n m nums den=
      FiniteWick.covarianceMajorant (positiveKernel n m h (1/10)) (tau total) := by
  funext u v
  have hc : (nums.getD (QuarticRowMajor.index n m (v-u)).val 0:ℝ)/(den:ℝ)=
      (endpointNumerator (kd.getD (QuarticRowMajor.index n m (v-u)).val 0):ℝ)/64000+
        (tauRational total:ℝ) := by
    exact_mod_cast hr (QuarticRowMajor.index n m (v-u))
  have hkv : kd.getD (QuarticRowMajor.index n m (v-u)).val 0=kernel n m u v :=
    congrFun (congrFun hk u) v
  rw [hkv,tauRational_cast] at hc
  simpa only [cachedCovariance,cachedNumerator,FiniteWick.covarianceMajorant,
    positiveKernel_endpoint n m h hi] using hc

/-- Nonnegativity is inherited from the identified actual covariance. -/
theorem cachedCovariance_nonneg_of_eq (nums : Array ℤ) (den total : ℕ)
    (h : Conditions n m)
    (he : cachedCovariance n m nums den=
      FiniteWick.covarianceMajorant (positiveKernel n m h (1/10)) (tau total))
    (u v : Torus.Vertex n m) : 0 ≤ cachedCovariance n m nums den u v := by
  rw [he]
  exact FiniteWick.covarianceMajorant_nonneg _ _ (fun _ _=>abs_nonneg _) (tau_nonneg total) u v

/-- Integer 9/3/3 contraction in precisely the physical matching orientation. -/
def matchingWeightNumerator (nums : Array ℤ) (sites : Fin 4→Torus.Vertex n m)
    (label : Fin 3) : ℤ :=
  let w := pairedSites sites label
  9*cachedNumerator n m nums (w 0) (w 1)*cachedNumerator n m nums (w 2) (w 3)+
  3*cachedNumerator n m nums (w 0) (w 2)*cachedNumerator n m nums (w 1) (w 3)+
  3*cachedNumerator n m nums (w 0) (w 3)*cachedNumerator n m nums (w 1) (w 2)

theorem matchingWeight_cached (nums : Array ℤ) (den : ℕ) (hden : 0 < den)
    (sites : Fin 4→Torus.Vertex n m) (label : Fin 3) :
    matchingWeight (cachedCovariance n m nums den) sites label=
      (matchingWeightNumerator n m nums sites label:ℝ)/(den:ℝ)^2 := by
  have hd : (den:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hden
  unfold matchingWeight matchingWeightNumerator cachedCovariance
  push_cast
  field_simp

end BilayerDressed.QuarticIntegerCovariance

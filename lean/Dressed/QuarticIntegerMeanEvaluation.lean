import Dressed.QuarticIntegerTable
import Dressed.QuarticIntegerEnvelopeBridge
import Dressed.QuarticIntegerCovarianceBase
import Dressed.QuarticCanonicalMean

/-! Actual canonical quartic means reduce to an exact finite integer weighted sum.
The signed coefficient identity is used before the absolute envelope. The physical
covariance weight is nonnegative. Rooted A/4 counting includes all supports and
stabilizers. The integer aggregate itself is a separate finite certificate.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerMeanEvaluation
open BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open QuarticIntegerArrays QuarticRootedRowTable QuarticIntegerTable
open QuarticPhysicalMean QuarticCanonicalMean QuarticIntegerCovariance
set_option maxHeartbeats 1500000

variable (n m R : ℕ) [NeZero (2*n)] [NeZero (2*m)]

/-- Exact integer aggregate, in the same row and matching order as the checked
signed table. Each matching weight includes the physical 9/3/3 contraction. -/
def weightedNumerator (raw : Array Row) (nums upper : Array ℤ)
    (ids : Array (Fin 3→ℕ)) : ℤ :=
  ∑ i : Fin R,∑ a : Fin 3,
    upper.getD ((ids.getD i.val 0) a) 0 *
      matchingWeightNumerator n m nums (sites n m (row raw i)) a

/-- Casting the integer sum introduces precisely the two stated denominators. -/
theorem weightedNumerator_evaluate (raw : Array Row) (nums upper : Array ℤ)
    (ids : Array (Fin 3→ℕ)) (upperDen covDen : ℕ) :
    (weightedNumerator n m R raw nums upper ids:ℝ)/((upperDen:ℝ)*(covDen:ℝ)^2)=
      ∑ i : Fin R,∑ a : Fin 3,
        (upper.getD ((ids.getD i.val 0) a) 0:ℝ)/(upperDen:ℝ) *
          ((matchingWeightNumerator n m nums (sites n m (row raw i)) a:ℝ)/(covDen:ℝ)^2) := by
  simp only [weightedNumerator,Int.cast_sum,Int.cast_mul,Finset.sum_div,div_mul_div_comm]

variable (kernelData : Array KernelCoefficients) (raw : Array Row)
variable (dictionary : Array Coefficients) (ids : Array (Fin 3→ℕ))
variable (hkernel : cachedKernel n m kernelData=kernel n m)
variable (hvalid : ∀ i : Fin R,Valid (area n m) (row raw i))
variable (hchecked : Checked n m R kernelData raw dictionary ids)
include hkernel hvalid hchecked

/-- Exact physical-to-table identity before any absolute coefficient bound. -/
theorem row_mean_eq (h : Conditions n m) (hi : IncidenceIdentity n m)
    (g : ℝ) (L : Torus.Vertex n m→Torus.Vertex n m→ℝ) (i : Fin R) :
    canonicalMeanWeight (QuarticRowMajor.enumeration n m) L
      (QuarticActualCoefficients.coefficient (QuarticRowMajor.enumeration n m)
        (cubicKernel (graph n m h) g) (Torus.xNext n m) (Torus.yNext n m) g)
      (supportRow n m raw R hvalid i)=
      ∑ a : Fin 3,|QuarticIntegerArrays.evaluate (expected dictionary ids i a) g/524288| *
        matchingWeight L (sites n m (row raw i)) a := by
  have hs : QuarticCanonical.tuple (QuarticRowMajor.enumeration n m)
      (supportRow n m raw R hvalid i)=sites n m (row raw i) :=
    rowMajor_sites_eq n m (row raw i) (hvalid i)
  unfold canonicalMeanWeight
  rw [hs]
  apply Finset.sum_congr rfl
  intro a _
  have hc := actual_coefficient n m R kernelData raw dictionary ids
    hkernel hvalid hchecked h hi g i a
  change CubicQuarticCoefficientCount.coefficient n m h g
    (supportRow n m raw R hvalid i) a=_ at hc
  exact congrArg (fun x : ℝ=>|x| * matchingWeight L (sites n m (row raw i)) a) hc

/-- The actual all-support mean is exactly the rooted table sum with factor A/4.
No free translation-action or fixed matching-order assumption is used. -/
theorem meanCoefficient_eq_rows (h : Conditions n m) (hi : IncidenceIdentity n m)
    (hcode : StrictMono (fun i : Fin R=>code (area n m) (row raw i)))
    (hcard : R=(area n m-1).choose 3) (g τ : ℝ) :
    meanCoefficient (QuarticRowMajor.enumeration n m) (cubicKernel (graph n m h) g)
      (Torus.xNext n m) (Torus.yNext n m) g
      (FiniteWick.covarianceMajorant (positiveKernel n m h (1/10)) τ)=
      (area n m:ℝ)/4 * ∑ i : Fin R,∑ a : Fin 3,
        |QuarticIntegerArrays.evaluate (expected dictionary ids i a) g/524288| *
          matchingWeight (FiniteWick.covarianceMajorant (positiveKernel n m h (1/10)) τ)
            (sites n m (row raw i)) a := by
  rw [cubic_mean_total_rooted,
    rootedMass_eq_sum_rows n m raw R hvalid hcode hcard]
  have hc : Fintype.card (Torus.Vertex n m)=area n m := by
    simp [area,Torus.Vertex,Fintype.card_prod]
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact row_mean_eq n m R kernelData raw dictionary ids hkernel hvalid hchecked h hi g _ i

/-- At each real g where the proved envelope applies, the actual quartic mean
is bounded by the exact finite integer weighted sum. No endpoint sampling is
used for the coefficient bound; only the covariance is its proved endpoint majorant. -/
theorem meanCoefficient_le_integer (h : Conditions n m) (hi : IncidenceIdentity n m)
    (hcode : StrictMono (fun i : Fin R=>code (area n m) (row raw i)))
    (hcard : R=(area n m-1).choose 3)
    (nums upper : Array ℤ) (covDen upperDen total : ℕ) (hcovDen : 0<covDen)
    (hcache : cachedCovariance n m nums covDen=
      FiniteWick.covarianceMajorant (positiveKernel n m h (1/10)) (tau total))
    (g : ℝ) (hbound : QuarticIntegerEnvelope.Bound dictionary upper upperDen g) :
    meanCoefficient (QuarticRowMajor.enumeration n m) (cubicKernel (graph n m h) g)
      (Torus.xNext n m) (Torus.yNext n m) g
      (FiniteWick.covarianceMajorant (positiveKernel n m h (1/10)) (tau total))≤
      (area n m:ℝ)/4 *
        ((weightedNumerator n m R raw nums upper ids:ℝ)/((upperDen:ℝ)*(covDen:ℝ)^2)) := by
  rw [meanCoefficient_eq_rows n m R kernelData raw dictionary ids hkernel hvalid hchecked
    h hi hcode hcard]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ i : Fin R,∑ a : Fin 3,
        (upper.getD ((ids.getD i.val 0) a) 0:ℝ)/(upperDen:ℝ) *
          matchingWeight (FiniteWick.covarianceMajorant (positiveKernel n m h (1/10))
            (tau total)) (sites n m (row raw i)) a := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_right (hbound ((ids.getD i.val 0) a))
      exact matchingWeight_nonneg _
        (FiniteWick.covarianceMajorant_nonneg _ _ (fun _ _=>abs_nonneg _) (tau_nonneg total)) _ _
    _ = _ := by
      rw [←hcache,weightedNumerator_evaluate]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      rw [matchingWeight_cached n m nums covDen hcovDen]

end BilayerDressed.QuarticIntegerMeanEvaluation

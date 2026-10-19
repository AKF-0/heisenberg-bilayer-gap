import Dressed.QuarticIntegerCovarianceBase
import Dressed.QuarticIntegerCovarianceData

/-! Kernel-checked exact covariance cache for the actual three seed graphs.
Every rational row identity is proved below, then transported to all site pairs
through the checked cubic kernel cache. There is no numerical-value premise.
-/
noncomputable section
namespace BilayerDressed.QuarticIntegerCovariance
open BilayerGap SeedGraphs CubicSeedChecks QuarticIntegerArrays QuarticIntegerCovarianceData
open QuarticPhysicalMean
set_option maxRecDepth 200000
set_option maxHeartbeats 1200000

/-- Exact rational arithmetic on the full finite row, including zero/default entries. -/
theorem row16_checked : ∀ q : Fin 16,
    (covarianceNumerators16.getD q.val 0:ℚ)/(covarianceDenominator16:ℚ)=
      (endpointNumerator (kernelData16.getD q.val 0):ℚ)/64000+tauRational 11597344 := by
  decide +kernel

/-- Actual global endpoint covariance equality, not just an upper estimate. -/
theorem cache16_eq :
    cachedCovariance 2 2 covarianceNumerators16 covarianceDenominator16=
      FiniteWick.covarianceMajorant (positiveKernel 2 2 four_by_four_conditions (1/10))
        (tau 11597344) :=
  cachedCovariance_eq 2 2 covarianceNumerators16 covarianceDenominator16 11597344
    kernelData16 four_by_four_conditions four_by_four_incidence cachedKernel16_eq row16_checked

theorem cache16_nonneg (u v : Torus.Vertex 2 2) :
    0 ≤ cachedCovariance 2 2 covarianceNumerators16 covarianceDenominator16 u v :=
  cachedCovariance_nonneg_of_eq 2 2 covarianceNumerators16 covarianceDenominator16
    11597344 four_by_four_conditions cache16_eq u v

/-- Exact integer normalization of the actual physical matching covariance weight. -/
theorem actual_weight16 (sites : Fin 4→Torus.Vertex 2 2) (label : Fin 3) :
    matchingWeight
      (FiniteWick.covarianceMajorant (positiveKernel 2 2 four_by_four_conditions (1/10))
        (tau 11597344)) sites label=
      (matchingWeightNumerator 2 2 covarianceNumerators16 sites label:ℝ)/
        (covarianceDenominator16:ℝ)^2 := by
  rw [←cache16_eq]
  exact matchingWeight_cached 2 2 covarianceNumerators16 covarianceDenominator16
    (by decide) sites label

/-- Exact rational arithmetic on the full finite row, including zero/default entries. -/
theorem row32_checked : ∀ q : Fin 32,
    (covarianceNumerators32.getD q.val 0:ℚ)/(covarianceDenominator32:ℚ)=
      (endpointNumerator (kernelData32.getD q.val 0):ℚ)/64000+tauRational 11548632 := by
  decide +kernel

/-- Actual global endpoint covariance equality, not just an upper estimate. -/
theorem cache32_eq :
    cachedCovariance 4 2 covarianceNumerators32 covarianceDenominator32=
      FiniteWick.covarianceMajorant (positiveKernel 4 2 eight_by_four_conditions (1/10))
        (tau 11548632) :=
  cachedCovariance_eq 4 2 covarianceNumerators32 covarianceDenominator32 11548632
    kernelData32 eight_by_four_conditions eight_by_four_incidence cachedKernel32_eq row32_checked

theorem cache32_nonneg (u v : Torus.Vertex 4 2) :
    0 ≤ cachedCovariance 4 2 covarianceNumerators32 covarianceDenominator32 u v :=
  cachedCovariance_nonneg_of_eq 4 2 covarianceNumerators32 covarianceDenominator32
    11548632 eight_by_four_conditions cache32_eq u v

/-- Exact integer normalization of the actual physical matching covariance weight. -/
theorem actual_weight32 (sites : Fin 4→Torus.Vertex 4 2) (label : Fin 3) :
    matchingWeight
      (FiniteWick.covarianceMajorant (positiveKernel 4 2 eight_by_four_conditions (1/10))
        (tau 11548632)) sites label=
      (matchingWeightNumerator 4 2 covarianceNumerators32 sites label:ℝ)/
        (covarianceDenominator32:ℝ)^2 := by
  rw [←cache32_eq]
  exact matchingWeight_cached 4 2 covarianceNumerators32 covarianceDenominator32
    (by decide) sites label

/-- Exact rational arithmetic on the full finite row, including zero/default entries. -/
theorem row64_checked : ∀ q : Fin 64,
    (covarianceNumerators64.getD q.val 0:ℚ)/(covarianceDenominator64:ℚ)=
      (endpointNumerator (kernelData64.getD q.val 0):ℚ)/64000+tauRational 11499920 := by
  decide +kernel

/-- Actual global endpoint covariance equality, not just an upper estimate. -/
theorem cache64_eq :
    cachedCovariance 4 4 covarianceNumerators64 covarianceDenominator64=
      FiniteWick.covarianceMajorant (positiveKernel 4 4 eight_by_eight_conditions (1/10))
        (tau 11499920) :=
  cachedCovariance_eq 4 4 covarianceNumerators64 covarianceDenominator64 11499920
    kernelData64 eight_by_eight_conditions eight_by_eight_incidence cachedKernel64_eq row64_checked

theorem cache64_nonneg (u v : Torus.Vertex 4 4) :
    0 ≤ cachedCovariance 4 4 covarianceNumerators64 covarianceDenominator64 u v :=
  cachedCovariance_nonneg_of_eq 4 4 covarianceNumerators64 covarianceDenominator64
    11499920 eight_by_eight_conditions cache64_eq u v

/-- Exact integer normalization of the actual physical matching covariance weight. -/
theorem actual_weight64 (sites : Fin 4→Torus.Vertex 4 4) (label : Fin 3) :
    matchingWeight
      (FiniteWick.covarianceMajorant (positiveKernel 4 4 eight_by_eight_conditions (1/10))
        (tau 11499920)) sites label=
      (matchingWeightNumerator 4 4 covarianceNumerators64 sites label:ℝ)/
        (covarianceDenominator64:ℝ)^2 := by
  rw [←cache64_eq]
  exact matchingWeight_cached 4 4 covarianceNumerators64 covarianceDenominator64
    (by decide) sites label

end BilayerDressed.QuarticIntegerCovariance

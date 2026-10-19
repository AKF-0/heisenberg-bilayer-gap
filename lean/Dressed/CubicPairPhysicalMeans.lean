import Dressed.CubicResidualIntervalBounds
import Dressed.PhysicalCreationCoefficients
import Dressed.CubicPhysicalMeanEndpoints

/-! The checked degree-two interval coefficient bounds become actual signed
hard-core residual means. No Wick, state, or coefficient premise remains. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicPairPhysicalMeans
open Matrix BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open FiniteOccupation FinitePhysicalWick CubicResidualPair

/-- The actual physical R2 component mean over the entire coupling interval. -/
theorem residual16_mean_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g),
      ((GlobalResidual.residual2 (cubicKernel (graph 2 2 four_by_four_conditions) g)
        (Torus.xNext 2 2) (Torus.yNext 2 2) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 2 2)) :
        ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin
          (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M16_0:ℝ)*(CubicResidualIntervalBounds.meanBound16:ℝ) := by
  rw [CubicResidualPolynomial.coe_residual2 2 2 four_by_four_conditions four_by_four_incidence]
  have h := CubicPhysicalMeans.four_by_four_physical_mean_endpoint g hg hmax
    (pairCoefficients (residual (graph 2 2 four_by_four_conditions) g)) pairWords
  rw [physicalPolynomial_pairs] at h
  simp only [modeCovariance] at h
  rw [pair_wick_coefficient] at h
  change _ ≤ (ScalarTrial.M16_0:ℝ)*pairMeanCoefficient 2 2 four_by_four_conditions g
    (FiniteWick.covarianceMajorant (positiveKernel 2 2 four_by_four_conditions (1/10)) (tau 11597344)) at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (CubicResidualIntervalBounds.pairMeanCoefficient_bound16 g hg hmax)
    (by norm_num [ScalarTrial.M16_0]))

/-- The actual physical R2 component mean over the entire coupling interval. -/
theorem residual32_mean_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g),
      ((GlobalResidual.residual2 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
        (Torus.xNext 4 2) (Torus.yNext 4 2) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 4 2)) :
        ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M32_0:ℝ)*(CubicResidualIntervalBounds.meanBound32:ℝ) := by
  rw [CubicResidualPolynomial.coe_residual2 4 2 eight_by_four_conditions eight_by_four_incidence]
  have h := CubicPhysicalMeans.eight_by_four_physical_mean_endpoint g hg hmax
    (pairCoefficients (residual (graph 4 2 eight_by_four_conditions) g)) pairWords
  rw [physicalPolynomial_pairs] at h
  simp only [modeCovariance] at h
  rw [pair_wick_coefficient] at h
  change _ ≤ (ScalarTrial.M32_0:ℝ)*pairMeanCoefficient 4 2 eight_by_four_conditions g
    (FiniteWick.covarianceMajorant (positiveKernel 4 2 eight_by_four_conditions (1/10)) (tau 11548632)) at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (CubicResidualIntervalBounds.pairMeanCoefficient_bound32 g hg hmax)
    (by norm_num [ScalarTrial.M32_0]))

/-- The actual physical R2 component mean over the entire coupling interval. -/
theorem residual64_mean_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g),
      ((GlobalResidual.residual2 (cubicKernel (graph 4 4 eight_by_eight_conditions) g)
        (Torus.xNext 4 4) (Torus.yNext 4 4) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 4 4)) :
        ConfigurationMatrix (Torus.Vertex 4 4)).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g))⟫| ≤
      (ScalarTrial.M64_0:ℝ)*(CubicResidualIntervalBounds.meanBound64:ℝ) := by
  rw [CubicResidualPolynomial.coe_residual2 4 4 eight_by_eight_conditions eight_by_eight_incidence]
  have h := CubicPhysicalMeans.eight_by_eight_physical_mean_endpoint g hg hmax
    (pairCoefficients (residual (graph 4 4 eight_by_eight_conditions) g)) pairWords
  rw [physicalPolynomial_pairs] at h
  simp only [modeCovariance] at h
  rw [pair_wick_coefficient] at h
  change _ ≤ (ScalarTrial.M64_0:ℝ)*pairMeanCoefficient 4 4 eight_by_eight_conditions g
    (FiniteWick.covarianceMajorant (positiveKernel 4 4 eight_by_eight_conditions (1/10)) (tau 11499920)) at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (CubicResidualIntervalBounds.pairMeanCoefficient_bound64 g hg hmax)
    (by norm_num [ScalarTrial.M64_0]))

end BilayerDressed.CubicPairPhysicalMeans

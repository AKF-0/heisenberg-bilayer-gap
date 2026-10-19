import Dressed.QuarticCanonicalMean

/-! Actual signed cubic residual4 physical means, reduced to the cancellation-
preserving finite canonical coefficient. The numerical envelope is deliberately
not assumed to have been proved by this bridge.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicQuarticPhysicalMeans
open Matrix BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open FiniteOccupation FinitePhysicalWick QuarticCanonicalMean

/-- The physical mean of the literal residual4, with its exact canonical coefficient. -/
theorem residual16_mean_le
    (enum : ∀ S : QuarticCanonical.Support (Torus.Vertex 2 2),Fin 4≃↥S.val)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g),
      ((GlobalResidual.residual4 (cubicKernel (graph 2 2 four_by_four_conditions) g)
        (Torus.xNext 2 2) (Torus.yNext 2 2) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 2 2)) :
        ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin
          (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M16_0:ℝ)*meanCoefficient enum
        (cubicKernel (graph 2 2 four_by_four_conditions) g)
        (Torus.xNext 2 2) (Torus.yNext 2 2) g
        (FiniteWick.covarianceMajorant (positiveKernel 2 2 four_by_four_conditions (1/10))
          (tau 11597344)) := by
  have hh := CubicPhysicalMeans.four_by_four_physical_mean_endpoint g hg hmax
    (coefficients enum (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g) (words enum)
  rw [physicalPolynomial_eq_residual4] at hh
  simp only [modeCovariance] at hh
  rw [wick_coefficient_eq] at hh
  exact hh

/-- The physical mean of the literal residual4, with its exact canonical coefficient. -/
theorem residual32_mean_le
    (enum : ∀ S : QuarticCanonical.Support (Torus.Vertex 4 2),Fin 4≃↥S.val)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g),
      ((GlobalResidual.residual4 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
        (Torus.xNext 4 2) (Torus.yNext 4 2) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 4 2)) :
        ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M32_0:ℝ)*meanCoefficient enum
        (cubicKernel (graph 4 2 eight_by_four_conditions) g)
        (Torus.xNext 4 2) (Torus.yNext 4 2) g
        (FiniteWick.covarianceMajorant (positiveKernel 4 2 eight_by_four_conditions (1/10))
          (tau 11548632)) := by
  have hh := CubicPhysicalMeans.eight_by_four_physical_mean_endpoint g hg hmax
    (coefficients enum (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g) (words enum)
  rw [physicalPolynomial_eq_residual4] at hh
  simp only [modeCovariance] at hh
  rw [wick_coefficient_eq] at hh
  exact hh

/-- The physical mean of the literal residual4, with its exact canonical coefficient. -/
theorem residual64_mean_le
    (enum : ∀ S : QuarticCanonical.Support (Torus.Vertex 4 4),Fin 4≃↥S.val)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g),
      ((GlobalResidual.residual4 (cubicKernel (graph 4 4 eight_by_eight_conditions) g)
        (Torus.xNext 4 4) (Torus.yNext 4 4) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 4 4)) :
        ConfigurationMatrix (Torus.Vertex 4 4)).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g))⟫| ≤
      (ScalarTrial.M64_0:ℝ)*meanCoefficient enum
        (cubicKernel (graph 4 4 eight_by_eight_conditions) g)
        (Torus.xNext 4 4) (Torus.yNext 4 4) g
        (FiniteWick.covarianceMajorant (positiveKernel 4 4 eight_by_eight_conditions (1/10))
          (tau 11499920)) := by
  have hh := CubicPhysicalMeans.eight_by_eight_physical_mean_endpoint g hg hmax
    (coefficients enum (cubicKernel (graph 4 4 eight_by_eight_conditions) g)
      (Torus.xNext 4 4) (Torus.yNext 4 4) g) (words enum)
  rw [physicalPolynomial_eq_residual4] at hh
  simp only [modeCovariance] at hh
  rw [wick_coefficient_eq] at hh
  exact hh

end BilayerDressed.CubicQuarticPhysicalMeans

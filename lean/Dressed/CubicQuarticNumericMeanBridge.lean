import Dressed.CubicQuarticPhysicalMeans
import Dressed.CubicQuarticMeanBudgets
import Dressed.CubicTrialSeedCriterion

/-! Final physical quartic-mean interfaces. The sole displayed numerical premise
is the actual finite canonical weighted coefficient bound. Its separate exact
integer/interval certificate must discharge this premise; none is assumed here.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicQuarticNumericMean
open Matrix BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open CubicTrialSeed QuarticCanonicalMean

/-- Exact actual finite coefficient certificate implies the physical R4 mean. -/
theorem mean16_of_coefficient
    (enum : ∀ S : QuarticCanonical.Support (Torus.Vertex 2 2),Fin 4≃↥S.val)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (hcoef : meanCoefficient enum (kernel16 g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g
      (FiniteWick.covarianceMajorant (positiveKernel 2 2 four_by_four_conditions (1/10))
        (tau 11597344)) ≤ (CubicQuarticSeed.meanBudget16:ℝ)) :
    |⟪dressedVector (kernel16 g),
      (GlobalResidual.residual4 (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g :
        ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin
          (dressedVector (kernel16 g))⟫| ≤
      (ScalarTrial.M16_0:ℝ)*(CubicQuarticSeed.meanBudget16:ℝ) :=
  (CubicQuarticPhysicalMeans.residual16_mean_le enum g hg hmax).trans
    (mul_le_mul_of_nonneg_left hcoef (by norm_num [ScalarTrial.M16_0]))

/-- Exact actual finite coefficient certificate implies the physical R4 mean. -/
theorem mean32_of_coefficient
    (enum : ∀ S : QuarticCanonical.Support (Torus.Vertex 4 2),Fin 4≃↥S.val)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (hcoef : meanCoefficient enum (kernel32 g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g
      (FiniteWick.covarianceMajorant (positiveKernel 4 2 eight_by_four_conditions (1/10))
        (tau 11548632)) ≤ (CubicQuarticSeed.meanBudget32:ℝ)) :
    |⟪dressedVector (kernel32 g),
      (GlobalResidual.residual4 (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g :
        ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin
          (dressedVector (kernel32 g))⟫| ≤
      (ScalarTrial.M32_0:ℝ)*(CubicQuarticSeed.meanBudget32:ℝ) :=
  (CubicQuarticPhysicalMeans.residual32_mean_le enum g hg hmax).trans
    (mul_le_mul_of_nonneg_left hcoef (by norm_num [ScalarTrial.M32_0]))

/-- Exact actual finite coefficient certificate implies the physical R4 mean. -/
theorem mean64_of_coefficient
    (enum : ∀ S : QuarticCanonical.Support (Torus.Vertex 4 4),Fin 4≃↥S.val)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (hcoef : meanCoefficient enum (kernel64 g)
      (Torus.xNext 4 4) (Torus.yNext 4 4) g
      (FiniteWick.covarianceMajorant (positiveKernel 4 4 eight_by_eight_conditions (1/10))
        (tau 11499920)) ≤ (CubicQuarticSeed.meanBudget64:ℝ)) :
    |⟪dressedVector (kernel64 g),
      (GlobalResidual.residual4 (kernel64 g) (Torus.xNext 4 4) (Torus.yNext 4 4) g :
        ConfigurationMatrix (Torus.Vertex 4 4)).toEuclideanLin
          (dressedVector (kernel64 g))⟫| ≤
      (ScalarTrial.M64_0:ℝ)*(CubicQuarticSeed.meanBudget64:ℝ) :=
  (CubicQuarticPhysicalMeans.residual64_mean_le enum g hg hmax).trans
    (mul_le_mul_of_nonneg_left hcoef (by norm_num [ScalarTrial.M64_0]))

end BilayerDressed.CubicQuarticNumericMean

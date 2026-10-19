import Dressed.QuarticIntegerActualNorm32
import Dressed.QuarticIntegerActualMean32
import Dressed.CubicQuarticNumericMeanBridge
import Dressed.CubicQuarticSeedReduction

import Dressed.CubicFourByFourEnergy
import Dressed.CubicSeedEnergyDefects

/-! Actual 8×4 energy/thermal and first spatial seed integration.
This bounded integration uses the complete 32-rung signed membership and physical
endpoint certificates. It does not require the 64-rung quartic mean and does not
assert an all-size gap or the other two spatial/thermal seed coordinates. -/
noncomputable section
open scoped RealInnerProductSpace
namespace BilayerDressed.CubicEightByFourEnergy
open BilayerGap GlobalResidual CubicTrialSeed CubicWick.FourRegularData
open CubicQuarticSeed ScalarInterval ScalarThermal

theorem residual_mean (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (kernel32 g),
      (CartesianBasis.fullHamiltonian 4 2 g).toEuclideanLin (dressedVector (kernel32 g))-
        shift32 g • dressedVector (kernel32 g)⟫| ≤ 346/1000000 := by
  have h4 := CubicQuarticNumericMean.mean32_of_coefficient
    (QuarticRowMajor.enumeration 4 2) g hg hmax (QuarticIntegerActual.mean32 g hg hmax)
  have hh := graph_residual_mean_le_of_components (kernel32 g)
    (cubicKernel_symmetric _ g) (Torus.xNext 4 2) (Torus.yNext 4 2)
    (Torus.xNext_ne 4 2 (by omega)) (Torus.yNext_ne 4 2 (by omega)) g
    ((ScalarTrial.M32_0:ℝ)*(CubicResidualIntervalBounds.meanBound32:ℝ))
    ((ScalarTrial.M32_0:ℝ)*(meanBudget32:ℝ))
    ((ScalarTrial.M32_0:ℝ)*(CubicSexticPhysicalMeans.coefficient32:ℝ))
    (CubicPairPhysicalMeans.residual32_mean_le g hg hmax) h4
    (CubicSexticPhysicalMeans.residual32_mean_le g hg hmax)
  rw [CubicResidualIntervalBounds.physical_residualShift_eq32 g] at hh
  have he : (ScalarTrial.M32_0:ℝ)*(CubicResidualIntervalBounds.meanBound32:ℝ)+
      (ScalarTrial.M32_0:ℝ)*(meanBudget32:ℝ)+
      (ScalarTrial.M32_0:ℝ)*(CubicSexticPhysicalMeans.coefficient32:ℝ) =
      (ScalarTrial.M32_0:ℝ)*(ScalarTrial.meanCoefficient32:ℝ) := by
    simp only [meanBudget32,Rat.cast_sub]
    ring
  rw [he] at hh
  apply hh.trans
  norm_num [ScalarTrial.M32_0,ScalarTrial.meanCoefficient32]

theorem residual_norm (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(CartesianBasis.fullHamiltonian 4 2 g).toEuclideanLin (dressedVector (kernel32 g))-
      shift32 g • dressedVector (kernel32 g)‖ ≤ 20172/1000000 := by
  have hh := CubicQuarticNormReduction.norm32 hg hmax
    (CubicPairAction.residual32_norm_le g hg hmax) (QuarticIntegerActual.vacuum32 g hg hmax)
  simpa only [CubicResidualIntervalBounds.physical_residualShift_eq32 g] using hh

theorem ground_upper (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g) ≤ shift32 g+346/1000000 :=
  CubicTrialEnergy.physical_upper 4 2 (by omega) (by omega) g
    (kernel32 g) (shift32 g) (346/1000000) (residual_mean g hg hmax)

theorem ground_lower (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    shift32 g-346/1000000-(20172/1000000:ℝ)^2/(den32:ℝ) ≤
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g) :=
  CubicTrialEnergy.physical_lower 4 2 (by omega) (by omega) g hg hmax
    (kernel32 g) (shift32 g) (346/1000000) (20172/1000000) (den32:ℝ)
    (residual_mean g hg hmax) (residual_norm g hg hmax) (by norm_num [den32])
    (by have hd := denominator32_lower hg hmax
        norm_num [a] at hd ⊢
        linarith)

theorem thermal (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian 8 4 g) 16 ≤
      (ScalarWarmup.Q1:ℝ) :=
  CubicSeedThermal.thermal32 hg hmax (ground_upper g hg hmax)

/-- The first correlated physical ground-energy defect is controlled on the
whole coupling interval; no 64-rung input is used. -/
theorem defect_x (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g)-
      2*groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) ≤
        (ScalarWarmup.dx:ℝ) :=
  CubicSeedEnergy.defect_x hg hmax
    (CubicFourByFourEnergy.ground_lower g hg hmax) (ground_upper g hg hmax)

/-- The first actual spatial purity defect at beta=16 satisfies its initial
warmup ceiling. The other two seed coordinates are not asserted here. -/
theorem spatial_seed_a (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    1-TraceConvexity.partition
        (Torus.fullHamiltonian 8 4 RealRungOperators.h RealRungOperators.G g) 16 /
      (TraceConvexity.partition
        (Torus.fullHamiltonian 4 4 RealRungOperators.h RealRungOperators.G g) 16)^2 ≤
      (ScalarWarmup.a0:ℝ) := by
  have hx := partition_spatial_ratio_lower
    (PhysicalGram.fullHamiltonian_hermitian 4 4 g)
    (PhysicalGram.fullHamiltonian_hermitian 8 4 g) 16 _ _ (by norm_num)
    (defect_x g hg hmax) (CubicFourByFourEnergy.thermal g hg hmax)
  have ha := ScalarThermal.initial_a_exponential
  push_cast at ha
  simp only [neg_mul] at hx
  linarith only [hx,ha]

end BilayerDressed.CubicEightByFourEnergy

import Dressed.QuarticIntegerActualNorm16
import Dressed.QuarticIntegerActualMean16
import Dressed.CubicQuarticNumericMeanBridge
import Dressed.CubicQuarticSeedReduction

/-! Complete actual 4×4 cubic-trial energy and thermal certificate through g=1/10.
This bounded integration checkpoint needs neither the 8×4 nor the 8×8 quartic
certificate. It is not an all-size gap theorem. -/
noncomputable section
open scoped RealInnerProductSpace
namespace BilayerDressed.CubicFourByFourEnergy
open BilayerGap GlobalResidual CubicTrialSeed CubicWick.FourRegularData
open CubicQuarticSeed ScalarInterval ScalarThermal

theorem residual_mean (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (kernel16 g),
      (CartesianBasis.fullHamiltonian 2 2 g).toEuclideanLin (dressedVector (kernel16 g))-
        shift16 g • dressedVector (kernel16 g)⟫| ≤ 167/1000000 := by
  have h4 := CubicQuarticNumericMean.mean16_of_coefficient
    (QuarticRowMajor.enumeration 2 2) g hg hmax (QuarticIntegerActual.mean16 g hg hmax)
  have hh := graph_residual_mean_le_of_components (kernel16 g)
    (cubicKernel_symmetric _ g) (Torus.xNext 2 2) (Torus.yNext 2 2)
    (Torus.xNext_ne 2 2 (by omega)) (Torus.yNext_ne 2 2 (by omega)) g
    ((ScalarTrial.M16_0:ℝ)*(CubicResidualIntervalBounds.meanBound16:ℝ))
    ((ScalarTrial.M16_0:ℝ)*(meanBudget16:ℝ))
    ((ScalarTrial.M16_0:ℝ)*(CubicSexticPhysicalMeans.coefficient16:ℝ))
    (CubicPairPhysicalMeans.residual16_mean_le g hg hmax) h4
    (CubicSexticPhysicalMeans.residual16_mean_le g hg hmax)
  rw [CubicResidualIntervalBounds.physical_residualShift_eq16 g] at hh
  have he : (ScalarTrial.M16_0:ℝ)*(CubicResidualIntervalBounds.meanBound16:ℝ)+
      (ScalarTrial.M16_0:ℝ)*(meanBudget16:ℝ)+
      (ScalarTrial.M16_0:ℝ)*(CubicSexticPhysicalMeans.coefficient16:ℝ) =
      (ScalarTrial.M16_0:ℝ)*(ScalarTrial.meanCoefficient16:ℝ) := by
    simp only [meanBudget16,Rat.cast_sub]
    ring
  rw [he] at hh
  apply hh.trans
  norm_num [ScalarTrial.M16_0,ScalarTrial.meanCoefficient16]

theorem residual_norm (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(CartesianBasis.fullHamiltonian 2 2 g).toEuclideanLin (dressedVector (kernel16 g))-
      shift16 g • dressedVector (kernel16 g)‖ ≤ 10982/1000000 := by
  have hh := CubicQuarticNormReduction.norm16 hg hmax
    (CubicPairAction.residual16_norm_le g hg hmax) (QuarticIntegerActual.vacuum16 g hg hmax)
  simpa only [CubicResidualIntervalBounds.physical_residualShift_eq16 g] using hh

theorem ground_upper (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) ≤ shift16 g+167/1000000 :=
  CubicTrialEnergy.physical_upper 2 2 (by omega) (by omega) g
    (kernel16 g) (shift16 g) (167/1000000) (residual_mean g hg hmax)

theorem ground_lower (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    shift16 g-167/1000000-(10982/1000000:ℝ)^2/(den16:ℝ) ≤
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) :=
  CubicTrialEnergy.physical_lower 2 2 (by omega) (by omega) g hg hmax
    (kernel16 g) (shift16 g) (167/1000000) (10982/1000000) (den16:ℝ)
    (residual_mean g hg hmax) (residual_norm g hg hmax) (by norm_num [den16])
    (by have hd := denominator16_lower hg hmax
        norm_num [a] at hd ⊢
        linarith)

theorem thermal (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian 4 4 g) 16 ≤
      (ScalarWarmup.Q0:ℝ) :=
  CubicSeedThermal.thermal16 hg hmax (ground_upper g hg hmax)

end BilayerDressed.CubicFourByFourEnergy

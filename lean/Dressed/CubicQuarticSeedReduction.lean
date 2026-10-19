import Dressed.CubicQuarticMeanBudgets
import Dressed.CubicQuarticNormReduction
import Dressed.CubicPairAction
import Dressed.CubicPairPhysicalMeans
import Dressed.CubicSexticPhysicalMeans

/-! All remaining actual cubic-trial obligations reduced to the quartic sector.
The physical pair and sextic components, scalar shifts, homogeneous amplification,
and the final Temple/thermal/warmup assembly are proved dependencies. This file
is still conditional on the explicitly displayed actual quartic certificates. -/
noncomputable section
open scoped RealInnerProductSpace
namespace BilayerDressed.CubicQuarticSeed
open BilayerGap GlobalResidual CubicTrialSeed CubicWick.FourRegularData

/-- Actual quartic quantities only. The coefficient/table proofs must construct
these fields; no unidentified scalar certificate is treated as physical data. -/
structure Inputs (g : ℝ) : Prop where
  mean16 : |⟪dressedVector (kernel16 g),
    (residual4 (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g :
      ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin (dressedVector (kernel16 g))⟫| ≤
      (ScalarTrial.M16_0:ℝ)*(meanBudget16:ℝ)
  mean32 : |⟪dressedVector (kernel32 g),
    (residual4 (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g :
      ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin (dressedVector (kernel32 g))⟫| ≤
      (ScalarTrial.M32_0:ℝ)*(meanBudget32:ℝ)
  mean64 : |⟪dressedVector (kernel64 g),
    (residual4 (kernel64 g) (Torus.xNext 4 4) (Torus.yNext 4 4) g :
      ConfigurationMatrix (Torus.Vertex 4 4)).toEuclideanLin (dressedVector (kernel64 g))⟫| ≤
      (ScalarTrial.M64_0:ℝ)*(meanBudget64:ℝ)
  vacuum16 : ‖(residual4 (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g :
    ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin vacuumVector‖^2 ≤ (ScalarTrial.F16_4:ℝ)
  vacuum32 : ‖(residual4 (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g :
    ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin vacuumVector‖^2 ≤ (ScalarTrial.F32_4:ℝ)

/-- Full actual Hamiltonian mean after the pair and sextic branches are discharged. -/
theorem mean16 {g : ℝ} (hg : 0 ≤ g) (hmax : g ≤ 1/10) (h : Inputs g) :
    |⟪dressedVector (kernel16 g),
      (CartesianBasis.fullHamiltonian 2 2 g).toEuclideanLin (dressedVector (kernel16 g))-
        ScalarInterval.shift16 g • dressedVector (kernel16 g)⟫| ≤ 167/1000000 := by
  have hh := graph_residual_mean_le_of_components (kernel16 g)
    (cubicKernel_symmetric _ g) (Torus.xNext 2 2) (Torus.yNext 2 2)
    (Torus.xNext_ne 2 2 (by omega)) (Torus.yNext_ne 2 2 (by omega)) g
    ((ScalarTrial.M16_0:ℝ)*(CubicResidualIntervalBounds.meanBound16:ℝ))
    ((ScalarTrial.M16_0:ℝ)*(meanBudget16:ℝ))
    ((ScalarTrial.M16_0:ℝ)*(CubicSexticPhysicalMeans.coefficient16:ℝ))
    (CubicPairPhysicalMeans.residual16_mean_le g hg hmax) h.mean16
    (CubicSexticPhysicalMeans.residual16_mean_le g hg hmax)
  have hs : residualShift (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g =
      ScalarInterval.shift16 g := CubicResidualIntervalBounds.physical_residualShift_eq16 g
  rw [hs] at hh
  have he : (ScalarTrial.M16_0:ℝ)*(CubicResidualIntervalBounds.meanBound16:ℝ)+
      (ScalarTrial.M16_0:ℝ)*(meanBudget16:ℝ)+
      (ScalarTrial.M16_0:ℝ)*(CubicSexticPhysicalMeans.coefficient16:ℝ) =
      (ScalarTrial.M16_0:ℝ)*(ScalarTrial.meanCoefficient16:ℝ) := by
    simp only [meanBudget16,Rat.cast_sub]
    ring
  rw [he] at hh
  apply hh.trans
  have hm : (ScalarTrial.M16_0:ℝ)*(ScalarTrial.meanCoefficient16:ℝ) < 167/1000000 := by
    norm_num [ScalarTrial.M16_0, ScalarTrial.meanCoefficient16]
  exact hm.le

/-- Full actual Hamiltonian mean after the pair and sextic branches are discharged. -/
theorem mean32 {g : ℝ} (hg : 0 ≤ g) (hmax : g ≤ 1/10) (h : Inputs g) :
    |⟪dressedVector (kernel32 g),
      (CartesianBasis.fullHamiltonian 4 2 g).toEuclideanLin (dressedVector (kernel32 g))-
        ScalarInterval.shift32 g • dressedVector (kernel32 g)⟫| ≤ 346/1000000 := by
  have hh := graph_residual_mean_le_of_components (kernel32 g)
    (cubicKernel_symmetric _ g) (Torus.xNext 4 2) (Torus.yNext 4 2)
    (Torus.xNext_ne 4 2 (by omega)) (Torus.yNext_ne 4 2 (by omega)) g
    ((ScalarTrial.M32_0:ℝ)*(CubicResidualIntervalBounds.meanBound32:ℝ))
    ((ScalarTrial.M32_0:ℝ)*(meanBudget32:ℝ))
    ((ScalarTrial.M32_0:ℝ)*(CubicSexticPhysicalMeans.coefficient32:ℝ))
    (CubicPairPhysicalMeans.residual32_mean_le g hg hmax) h.mean32
    (CubicSexticPhysicalMeans.residual32_mean_le g hg hmax)
  have hs : residualShift (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g =
      ScalarInterval.shift32 g := CubicResidualIntervalBounds.physical_residualShift_eq32 g
  rw [hs] at hh
  have he : (ScalarTrial.M32_0:ℝ)*(CubicResidualIntervalBounds.meanBound32:ℝ)+
      (ScalarTrial.M32_0:ℝ)*(meanBudget32:ℝ)+
      (ScalarTrial.M32_0:ℝ)*(CubicSexticPhysicalMeans.coefficient32:ℝ) =
      (ScalarTrial.M32_0:ℝ)*(ScalarTrial.meanCoefficient32:ℝ) := by
    simp only [meanBudget32,Rat.cast_sub]
    ring
  rw [he] at hh
  apply hh.trans
  have hm : (ScalarTrial.M32_0:ℝ)*(ScalarTrial.meanCoefficient32:ℝ) < 346/1000000 := by
    norm_num [ScalarTrial.M32_0, ScalarTrial.meanCoefficient32]
  exact hm.le

/-- Full actual Hamiltonian mean after the pair and sextic branches are discharged. -/
theorem mean64 {g : ℝ} (hg : 0 ≤ g) (hmax : g ≤ 1/10) (h : Inputs g) :
    |⟪dressedVector (kernel64 g),
      (CartesianBasis.fullHamiltonian 4 4 g).toEuclideanLin (dressedVector (kernel64 g))-
        ScalarInterval.shift64 g • dressedVector (kernel64 g)⟫| ≤ 800/1000000 := by
  have hh := graph_residual_mean_le_of_components (kernel64 g)
    (cubicKernel_symmetric _ g) (Torus.xNext 4 4) (Torus.yNext 4 4)
    (Torus.xNext_ne 4 4 (by omega)) (Torus.yNext_ne 4 4 (by omega)) g
    ((ScalarTrial.M64_0:ℝ)*(CubicResidualIntervalBounds.meanBound64:ℝ))
    ((ScalarTrial.M64_0:ℝ)*(meanBudget64:ℝ))
    ((ScalarTrial.M64_0:ℝ)*(CubicSexticPhysicalMeans.coefficient64:ℝ))
    (CubicPairPhysicalMeans.residual64_mean_le g hg hmax) h.mean64
    (CubicSexticPhysicalMeans.residual64_mean_le g hg hmax)
  have hs : residualShift (kernel64 g) (Torus.xNext 4 4) (Torus.yNext 4 4) g =
      ScalarInterval.shift64 g := CubicResidualIntervalBounds.physical_residualShift_eq64 g
  rw [hs] at hh
  have he : (ScalarTrial.M64_0:ℝ)*(CubicResidualIntervalBounds.meanBound64:ℝ)+
      (ScalarTrial.M64_0:ℝ)*(meanBudget64:ℝ)+
      (ScalarTrial.M64_0:ℝ)*(CubicSexticPhysicalMeans.coefficient64:ℝ) =
      (ScalarTrial.M64_0:ℝ)*(ScalarTrial.meanCoefficient64:ℝ) := by
    simp only [meanBudget64,Rat.cast_sub]
    ring
  rw [he] at hh
  apply hh.trans
  have hm : (ScalarTrial.M64_0:ℝ)*(ScalarTrial.meanCoefficient64:ℝ) < 800/1000000 := by
    norm_num [ScalarTrial.M64_0, ScalarTrial.meanCoefficient64]
  exact hm.le

/-- Full actual residual norm after the pair and sextic branches are discharged. -/
theorem norm16 {g : ℝ} (hg : 0 ≤ g) (hmax : g ≤ 1/10) (h : Inputs g) :
    ‖(CartesianBasis.fullHamiltonian 2 2 g).toEuclideanLin (dressedVector (kernel16 g))-
      ScalarInterval.shift16 g • dressedVector (kernel16 g)‖ ≤ 10982/1000000 := by
  have hh := CubicQuarticNormReduction.norm16 hg hmax
    (CubicPairAction.residual16_norm_le g hg hmax) h.vacuum16
  have hs : residualShift (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g =
      ScalarInterval.shift16 g := CubicResidualIntervalBounds.physical_residualShift_eq16 g
  simpa only [hs] using hh

/-- Full actual residual norm after the pair and sextic branches are discharged. -/
theorem norm32 {g : ℝ} (hg : 0 ≤ g) (hmax : g ≤ 1/10) (h : Inputs g) :
    ‖(CartesianBasis.fullHamiltonian 4 2 g).toEuclideanLin (dressedVector (kernel32 g))-
      ScalarInterval.shift32 g • dressedVector (kernel32 g)‖ ≤ 20172/1000000 := by
  have hh := CubicQuarticNormReduction.norm32 hg hmax
    (CubicPairAction.residual32_norm_le g hg hmax) h.vacuum32
  have hs : residualShift (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g =
      ScalarInterval.shift32 g := CubicResidualIntervalBounds.physical_residualShift_eq32 g
  simpa only [hs] using hh

/-- The five remaining actual quartic certificates construct the complete actual
cubic-trial input. This theorem does not construct those quartic certificates. -/
theorem trial_bounds {g : ℝ} (hg : 0 ≤ g) (hmax : g ≤ 1/10) (h : Inputs g) :
    CubicTrialSeed.Bounds g :=
  ⟨mean16 hg hmax h,mean32 hg hmax h,mean64 hg hmax h,
    norm16 hg hmax h,norm32 hg hmax h⟩

end BilayerDressed.CubicQuarticSeed

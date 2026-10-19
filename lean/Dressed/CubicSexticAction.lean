import Dressed.CubicSexticMass
import Dressed.CubicTrialNormCertificates

/-! Actual degree-six residual action on the physical cubic dressed vector.
The finite bosonic estimate is transported by the proved one-sided faithful
intertwiner and contractive physical projection, not by a norm equality. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicSexticAction
open Matrix BilayerGap SeedGraphs CubicSeedChecks SexticFaithfulLift
open CubicWick.FourRegularData FiniteOccupation
open TotalCutoff.PairNorm TotalCutoff.PairHomogeneous
set_option maxHeartbeats 1000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The homogeneous amplification vacuum is the genuine faithful seed. -/
theorem homogeneous_seed_eq {V : Type*} [Fintype V] [DecidableEq V] {M N : ℕ}
    (K : V → V → ℝ) (ex ey : V → V) (g : ℝ) :
    homogeneousAction 6 (faithfulCoefficients K ex ey g)
      (TotalCutoff.PairNorm.vacuumVector : Hilbert V M N) =
      vacuumImage (faithfulResidual6 K ex ey g : TotalCutoff.Op V M N) := by
  unfold homogeneousAction
  rw [← faithfulResidual6_eq_homogeneous]
  rfl

/-- Finite faithful degree-six action with all scalar premises discharged. -/
theorem lift16_norm_le {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(faithfulResidual6 (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g : TotalCutoff.Op (Torus.Vertex 2 2) M N).toEuclideanLin
      (finiteTrial (CubicPairNorm.modeKernel 2 2 four_by_four_conditions g) 8)‖ ≤
      (ScalarTrial.e16_6 : ℝ) := by
  rw [faithfulResidual6_eq_homogeneous]
  change ‖homogeneousAction 6 _ _‖ ≤ _
  have ha := CubicTrialNorm.homogeneous16_6_norm_sq_le (M := M) (N := N) hNM hN g hg hmax
    (faithfulCoefficients (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g)
  rw [homogeneous_seed_eq] at ha
  have hb := CubicSexticMass.vacuum16_norm_sq_le (M := M) (N := N) hNM hN g hg hmax
  have hm : 0 ≤ (ScalarTrial.M16_6 : ℝ) := by norm_num [ScalarTrial.M16_6]
  have hs : (ScalarTrial.F16_6 : ℝ) * (ScalarTrial.M16_6 : ℝ) ≤
      (ScalarTrial.e16_6 : ℝ)^2 := by exact_mod_cast ScalarTrial.root16_6.2
  have he : 0 < (ScalarTrial.e16_6 : ℝ) := by exact_mod_cast ScalarTrial.root16_6.1
  have hh := ha.trans ((mul_le_mul_of_nonneg_right hb hm).trans hs)
  nlinarith [norm_nonneg (homogeneousAction 6
    (faithfulCoefficients (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g)
    (finiteTrial (CubicPairNorm.modeKernel 2 2 four_by_four_conditions g) 8 : Hilbert (Torus.Vertex 2 2) M N))]

/-- Genuine physical residual6 action, uniformly for every 0 ≤ g ≤ .1. -/
theorem residual16_norm_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(GlobalResidual.residual6 (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g : ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin
      (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g))‖ ≤ (ScalarTrial.e16_6 : ℝ) := by
  have hp := FiniteDressed.physical_action_dressed_norm_le (M := 16) (by omega)
    (cubicKernel (graph 2 2 four_by_four_conditions) g)
    (faithfulResidual6 (cubicKernel (graph 2 2 four_by_four_conditions) g) (Torus.xNext 2 2) (Torus.yNext 2 2) g)
    (GlobalResidual.residual6 (cubicKernel (graph 2 2 four_by_four_conditions) g) (Torus.xNext 2 2) (Torus.yNext 2 2) g)
    (physical_transpose_faithfulResidual6 (by omega) _ _ _ _)
  apply hp.trans
  simpa [Torus.Vertex, FiniteDressed.modeKernel, CubicPairNorm.modeKernel] using
    lift16_norm_le (M := 16) (N := 16) (by omega) (by omega) g hg hmax

/-- Finite faithful degree-six action with all scalar premises discharged. -/
theorem lift32_norm_le {M N : ℕ} (hNM : N ≤ M) (hN : 6 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(faithfulResidual6 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g : TotalCutoff.Op (Torus.Vertex 4 2) M N).toEuclideanLin
      (finiteTrial (CubicPairNorm.modeKernel 4 2 eight_by_four_conditions g) 16)‖ ≤
      (ScalarTrial.e32_6 : ℝ) := by
  rw [faithfulResidual6_eq_homogeneous]
  change ‖homogeneousAction 6 _ _‖ ≤ _
  have ha := CubicTrialNorm.homogeneous32_6_norm_sq_le (M := M) (N := N) hNM hN g hg hmax
    (faithfulCoefficients (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g)
  rw [homogeneous_seed_eq] at ha
  have hb := CubicSexticMass.vacuum32_norm_sq_le (M := M) (N := N) hNM hN g hg hmax
  have hm : 0 ≤ (ScalarTrial.M32_6 : ℝ) := by norm_num [ScalarTrial.M32_6]
  have hs : (ScalarTrial.F32_6 : ℝ) * (ScalarTrial.M32_6 : ℝ) ≤
      (ScalarTrial.e32_6 : ℝ)^2 := by exact_mod_cast ScalarTrial.root32_6.2
  have he : 0 < (ScalarTrial.e32_6 : ℝ) := by exact_mod_cast ScalarTrial.root32_6.1
  have hh := ha.trans ((mul_le_mul_of_nonneg_right hb hm).trans hs)
  nlinarith [norm_nonneg (homogeneousAction 6
    (faithfulCoefficients (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g)
    (finiteTrial (CubicPairNorm.modeKernel 4 2 eight_by_four_conditions g) 16 : Hilbert (Torus.Vertex 4 2) M N))]

/-- Genuine physical residual6 action, uniformly for every 0 ≤ g ≤ .1. -/
theorem residual32_norm_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(GlobalResidual.residual6 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g : ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin
      (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g))‖ ≤ (ScalarTrial.e32_6 : ℝ) := by
  have hp := FiniteDressed.physical_action_dressed_norm_le (M := 32) (by omega)
    (cubicKernel (graph 4 2 eight_by_four_conditions) g)
    (faithfulResidual6 (cubicKernel (graph 4 2 eight_by_four_conditions) g) (Torus.xNext 4 2) (Torus.yNext 4 2) g)
    (GlobalResidual.residual6 (cubicKernel (graph 4 2 eight_by_four_conditions) g) (Torus.xNext 4 2) (Torus.yNext 4 2) g)
    (physical_transpose_faithfulResidual6 (by omega) _ _ _ _)
  apply hp.trans
  simpa [Torus.Vertex, FiniteDressed.modeKernel, CubicPairNorm.modeKernel] using
    lift32_norm_le (M := 32) (N := 32) (by omega) (by omega) g hg hmax

end BilayerDressed.CubicSexticAction

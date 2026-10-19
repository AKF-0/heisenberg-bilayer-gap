import Dressed.ConcreteQuarticResidualLift
import Dressed.CubicTrialNormCertificates
import Dressed.FiniteDressedProjection

/-! Actual quartic residual action on the physical cubic dressed vector.
Only the explicitly displayed physical vacuum F4 bound remains conditional.
The finite homogeneous amplification, signed cubic pair majorant, rational
square-root envelope, and physical projection are all proved inputs. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticDressedAction
open Matrix BilayerGap SeedGraphs CubicSeedChecks FiniteOccupation
open CubicWick.FourRegularData ConcreteQuarticLift
open TotalCutoff.PairNorm TotalCutoff.PairHomogeneous
set_option maxHeartbeats 500000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The homogeneous vacuum constant is exactly the literal physical R4 seed. -/
theorem homogeneous_seed_norm_eq {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} (hM : 2 ≤ M) (K : V → V → ℝ) (ex ey : V ≃ V) (g : ℝ) :
    ‖homogeneousAction 4 (homogeneousCoefficient K ex ey g)
      (TotalCutoff.PairNorm.vacuumVector : Hilbert V M (Fintype.card V))‖ =
      ‖(GlobalResidual.residual4 K ex ey g : ConfigurationMatrix V).toEuclideanLin
        BilayerDressed.vacuumVector‖ := by
  unfold homogeneousAction
  rw [← operator_eq_homogeneous]
  exact operator_vacuum_norm_eq hM K ex ey g

/-- Actual finite quartic action; the only residual-specific premise is the
physical vacuum norm bound, not a bosonic norm or amplification assumption. -/
theorem lift16_norm_le {M : ℕ} (hM : 16 ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (hF : ‖(GlobalResidual.residual4 (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g : ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin
        BilayerDressed.vacuumVector‖ ^ 2 ≤ (ScalarTrial.F16_4 : ℝ)) :
    ‖(operator (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g : TotalCutoff.Op (Torus.Vertex 2 2) M (Fintype.card (Torus.Vertex 2 2))).toEuclideanLin
      (finiteTrial (CubicPairNorm.modeKernel 2 2 four_by_four_conditions g) 8)‖ ≤
      (ScalarTrial.e16_4 : ℝ) := by
  rw [operator_eq_homogeneous]
  change ‖homogeneousAction 4 _ _‖ ≤ _
  have ha := CubicTrialNorm.homogeneous16_4_norm_sq_le
    (M := M) (N := Fintype.card (Torus.Vertex 2 2))
    (by simpa [Torus.Vertex] using hM) (by norm_num [Torus.Vertex]) g hg hmax
    (homogeneousCoefficient (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g)
  rw [homogeneous_seed_norm_eq (by omega)] at ha
  have hm : 0 ≤ (ScalarTrial.M16_4 : ℝ) := by norm_num [ScalarTrial.M16_4]
  have hs : (ScalarTrial.F16_4 : ℝ) * (ScalarTrial.M16_4 : ℝ) ≤
      (ScalarTrial.e16_4 : ℝ)^2 := by exact_mod_cast ScalarTrial.root16_4.2
  have he : 0 < (ScalarTrial.e16_4 : ℝ) := by exact_mod_cast ScalarTrial.root16_4.1
  have hh := ha.trans ((mul_le_mul_of_nonneg_right hF hm).trans hs)
  nlinarith [norm_nonneg (homogeneousAction 4
    (homogeneousCoefficient (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g)
    (finiteTrial (CubicPairNorm.modeKernel 2 2 four_by_four_conditions g) 8 :
      Hilbert (Torus.Vertex 2 2) M (Fintype.card (Torus.Vertex 2 2))))]

/-- Genuine physical R4 action on the signed cubic dressed vector, conditional
only on its displayed actual vacuum F4 certificate. -/
theorem residual16_norm_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (hF : ‖(GlobalResidual.residual4 (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g : ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin
        BilayerDressed.vacuumVector‖ ^ 2 ≤ (ScalarTrial.F16_4 : ℝ)) :
    ‖(GlobalResidual.residual4 (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g : ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin
      (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g))‖ ≤ (ScalarTrial.e16_4 : ℝ) := by
  have hp := FiniteDressed.physical_action_dressed_norm_le (M := 16) (by omega)
    (cubicKernel (graph 2 2 four_by_four_conditions) g)
    (operator (cubicKernel (graph 2 2 four_by_four_conditions) g) (Torus.xNext 2 2) (Torus.yNext 2 2) g)
    (GlobalResidual.residual4 (cubicKernel (graph 2 2 four_by_four_conditions) g) (Torus.xNext 2 2) (Torus.yNext 2 2) g)
    (operator_intertwiner (by omega) _ _ _ _)
  apply hp.trans
  simpa [Torus.Vertex, FiniteDressed.modeKernel, CubicPairNorm.modeKernel] using
    lift16_norm_le (M := 16) (by omega) g hg hmax hF

/-- Actual finite quartic action; the only residual-specific premise is the
physical vacuum norm bound, not a bosonic norm or amplification assumption. -/
theorem lift32_norm_le {M : ℕ} (hM : 32 ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (hF : ‖(GlobalResidual.residual4 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g : ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin
        BilayerDressed.vacuumVector‖ ^ 2 ≤ (ScalarTrial.F32_4 : ℝ)) :
    ‖(operator (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g : TotalCutoff.Op (Torus.Vertex 4 2) M (Fintype.card (Torus.Vertex 4 2))).toEuclideanLin
      (finiteTrial (CubicPairNorm.modeKernel 4 2 eight_by_four_conditions g) 16)‖ ≤
      (ScalarTrial.e32_4 : ℝ) := by
  rw [operator_eq_homogeneous]
  change ‖homogeneousAction 4 _ _‖ ≤ _
  have ha := CubicTrialNorm.homogeneous32_4_norm_sq_le
    (M := M) (N := Fintype.card (Torus.Vertex 4 2))
    (by simpa [Torus.Vertex] using hM) (by norm_num [Torus.Vertex]) g hg hmax
    (homogeneousCoefficient (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g)
  rw [homogeneous_seed_norm_eq (by omega)] at ha
  have hm : 0 ≤ (ScalarTrial.M32_4 : ℝ) := by norm_num [ScalarTrial.M32_4]
  have hs : (ScalarTrial.F32_4 : ℝ) * (ScalarTrial.M32_4 : ℝ) ≤
      (ScalarTrial.e32_4 : ℝ)^2 := by exact_mod_cast ScalarTrial.root32_4.2
  have he : 0 < (ScalarTrial.e32_4 : ℝ) := by exact_mod_cast ScalarTrial.root32_4.1
  have hh := ha.trans ((mul_le_mul_of_nonneg_right hF hm).trans hs)
  nlinarith [norm_nonneg (homogeneousAction 4
    (homogeneousCoefficient (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g)
    (finiteTrial (CubicPairNorm.modeKernel 4 2 eight_by_four_conditions g) 16 :
      Hilbert (Torus.Vertex 4 2) M (Fintype.card (Torus.Vertex 4 2))))]

/-- Genuine physical R4 action on the signed cubic dressed vector, conditional
only on its displayed actual vacuum F4 certificate. -/
theorem residual32_norm_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (hF : ‖(GlobalResidual.residual4 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g : ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin
        BilayerDressed.vacuumVector‖ ^ 2 ≤ (ScalarTrial.F32_4 : ℝ)) :
    ‖(GlobalResidual.residual4 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g : ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin
      (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g))‖ ≤ (ScalarTrial.e32_4 : ℝ) := by
  have hp := FiniteDressed.physical_action_dressed_norm_le (M := 32) (by omega)
    (cubicKernel (graph 4 2 eight_by_four_conditions) g)
    (operator (cubicKernel (graph 4 2 eight_by_four_conditions) g) (Torus.xNext 4 2) (Torus.yNext 4 2) g)
    (GlobalResidual.residual4 (cubicKernel (graph 4 2 eight_by_four_conditions) g) (Torus.xNext 4 2) (Torus.yNext 4 2) g)
    (operator_intertwiner (by omega) _ _ _ _)
  apply hp.trans
  simpa [Torus.Vertex, FiniteDressed.modeKernel, CubicPairNorm.modeKernel] using
    lift32_norm_le (M := 32) (by omega) g hg hmax hF

end BilayerDressed.QuarticDressedAction

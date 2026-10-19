import Dressed.CubicPairHomogeneousBounds
import Dressed.CubicTrialNormCertificates

/-! Actual degree-two residual action on the signed physical cubic trial.
The vacuum certificate, finite homogeneous amplification, and one-sided
physical intertwiner are all proved for the actual matrices. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicPairAction
open Matrix BilayerGap SeedGraphs CubicSeedChecks CubicPairHomogeneous
open CubicWick.FourRegularData FiniteOccupation
open TotalCutoff.PairNorm TotalCutoff.PairHomogeneous
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

/-- Actual pair compression transports the signed dressed action at abstract V. -/
theorem physical_pair_action_norm_le {V : Type*} [Fintype V] [DecidableEq V]
    {M : ℕ} (hM : 2≤M) (K F : Matrix V V ℝ) :
    ‖(pairKernelS F).toEuclideanLin (dressedVector K)‖ ≤
      ‖(TotalCutoff.Pair.pairCreate (FiniteDressed.modeKernel F) :
        TotalCutoff.Op V M (Fintype.card V)).toEuclideanLin
          (finiteTrial (FiniteDressed.modeKernel K) (Fintype.card V/2))‖ :=
  FiniteDressed.physical_action_dressed_norm_le hM K _ _
    (FiniteDressed.physical_transpose_pair hM F)

theorem lift16_norm_le {M N : ℕ} (hNM : N≤M) (hN : 2≤N)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ‖(TotalCutoff.Pair.pairCreate
      (FiniteDressed.modeKernel (CubicResidualPair.residual (graph 2 2 four_by_four_conditions) g)) :
        TotalCutoff.Op (Torus.Vertex 2 2) M N).toEuclideanLin
      (finiteTrial (CubicPairNorm.modeKernel 2 2 four_by_four_conditions g) 8)‖≤
        (ScalarTrial.e16_2 : ℝ) := by
  rw [pairCreate_eq_homogeneous]
  change ‖homogeneousAction 2 (residualCoefficients (graph 2 2 four_by_four_conditions) g) _‖≤_
  have ha := CubicTrialNorm.homogeneous16_2_norm_sq_le (M := M) (N := N) hNM hN g hg hmax
    (residualCoefficients (graph 2 2 four_by_four_conditions) g)
  have hb := residual_vacuum_norm_sq_bound16 (M := M) (N := N) hNM hN g hg hmax
  change ‖homogeneousAction 2 _ (TotalCutoff.PairNorm.vacuumVector :
    Hilbert (Torus.Vertex 2 2) M N)‖^2≤(ScalarTrial.F16_2 : ℝ) at hb
  have hm : 0≤(ScalarTrial.M16_2 : ℝ) := by norm_num [ScalarTrial.M16_2]
  have hs : (ScalarTrial.F16_2 : ℝ)*(ScalarTrial.M16_2 : ℝ)≤
      (ScalarTrial.e16_2 : ℝ)^2 := by exact_mod_cast ScalarTrial.root16_2.2
  have he : 0<(ScalarTrial.e16_2 : ℝ) := by exact_mod_cast ScalarTrial.root16_2.1
  have hh := ha.trans ((mul_le_mul_of_nonneg_right hb hm).trans hs)
  nlinarith [norm_nonneg (homogeneousAction 2
    (residualCoefficients (graph 2 2 four_by_four_conditions) g)
    (finiteTrial (CubicPairNorm.modeKernel 2 2 four_by_four_conditions g) 8 :
      Hilbert (Torus.Vertex 2 2) M N))]

/-- The literal physical residual2 on the signed dressed state, throughout [0,.1]. -/
theorem residual16_norm_le (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ‖(GlobalResidual.residual2 (cubicKernel (graph 2 2 four_by_four_conditions) g)
      (Torus.xNext 2 2) (Torus.yNext 2 2) g : ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin
      (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g))‖≤(ScalarTrial.e16_2 : ℝ) := by
  rw [CubicResidualPolynomial.coe_residual2 2 2 four_by_four_conditions four_by_four_incidence]
  have hp := physical_pair_action_norm_le (M := 16) (by omega)
    (cubicKernel (graph 2 2 four_by_four_conditions) g)
    (CubicResidualPair.residual (graph 2 2 four_by_four_conditions) g)
  apply hp.trans
  simpa [Torus.Vertex,FiniteDressed.modeKernel,CubicPairNorm.modeKernel] using
    lift16_norm_le (M := 16) (N := 16) (by omega) (by omega) g hg hmax

theorem lift32_norm_le {M N : ℕ} (hNM : N≤M) (hN : 2≤N)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ‖(TotalCutoff.Pair.pairCreate
      (FiniteDressed.modeKernel (CubicResidualPair.residual (graph 4 2 eight_by_four_conditions) g)) :
        TotalCutoff.Op (Torus.Vertex 4 2) M N).toEuclideanLin
      (finiteTrial (CubicPairNorm.modeKernel 4 2 eight_by_four_conditions g) 16)‖≤
        (ScalarTrial.e32_2 : ℝ) := by
  rw [pairCreate_eq_homogeneous]
  change ‖homogeneousAction 2 (residualCoefficients (graph 4 2 eight_by_four_conditions) g) _‖≤_
  have ha := CubicTrialNorm.homogeneous32_2_norm_sq_le (M := M) (N := N) hNM hN g hg hmax
    (residualCoefficients (graph 4 2 eight_by_four_conditions) g)
  have hb := residual_vacuum_norm_sq_bound32 (M := M) (N := N) hNM hN g hg hmax
  change ‖homogeneousAction 2 _ (TotalCutoff.PairNorm.vacuumVector :
    Hilbert (Torus.Vertex 4 2) M N)‖^2≤(ScalarTrial.F32_2 : ℝ) at hb
  have hm : 0≤(ScalarTrial.M32_2 : ℝ) := by norm_num [ScalarTrial.M32_2]
  have hs : (ScalarTrial.F32_2 : ℝ)*(ScalarTrial.M32_2 : ℝ)≤
      (ScalarTrial.e32_2 : ℝ)^2 := by exact_mod_cast ScalarTrial.root32_2.2
  have he : 0<(ScalarTrial.e32_2 : ℝ) := by exact_mod_cast ScalarTrial.root32_2.1
  have hh := ha.trans ((mul_le_mul_of_nonneg_right hb hm).trans hs)
  nlinarith [norm_nonneg (homogeneousAction 2
    (residualCoefficients (graph 4 2 eight_by_four_conditions) g)
    (finiteTrial (CubicPairNorm.modeKernel 4 2 eight_by_four_conditions g) 16 :
      Hilbert (Torus.Vertex 4 2) M N))]

/-- The literal physical residual2 on the signed dressed state, throughout [0,.1]. -/
theorem residual32_norm_le (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ‖(GlobalResidual.residual2 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
      (Torus.xNext 4 2) (Torus.yNext 4 2) g : ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin
      (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g))‖≤(ScalarTrial.e32_2 : ℝ) := by
  rw [CubicResidualPolynomial.coe_residual2 4 2 eight_by_four_conditions eight_by_four_incidence]
  have hp := physical_pair_action_norm_le (M := 32) (by omega)
    (cubicKernel (graph 4 2 eight_by_four_conditions) g)
    (CubicResidualPair.residual (graph 4 2 eight_by_four_conditions) g)
  apply hp.trans
  simpa [Torus.Vertex,FiniteDressed.modeKernel,CubicPairNorm.modeKernel] using
    lift32_norm_le (M := 32) (N := 32) (by omega) (by omega) g hg hmax

end BilayerDressed.CubicPairAction

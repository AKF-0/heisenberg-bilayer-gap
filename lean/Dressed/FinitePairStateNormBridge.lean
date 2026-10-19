import Dressed.CubicTrialNormCertificates
import Dressed.CubicFiniteMoments

/-!
# Exact positive finite Taylor state and Hilbert norm alignment

The raw state used by finite Wick inequalities is exactly the finite Hilbert
Taylor vector. Both sums include powers zero through L, with identical actual
total-cutoff matrices. No infinite exponential or equality with a signed state
is involved.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FiniteOccupation.TotalCutoff.PairStateBridge
open Matrix PairNorm PositiveMoments
set_option maxHeartbeats 3000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact raw-vector identification, for arbitrary real kernels and every cutoff. -/
theorem pairState_eq_ofLp_finiteTrial {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (L : ℕ) :
    pairState (M := M) (N := N) B L =
      WithLp.ofLp (finiteTrial B L : Hilbert V M N) := by
  unfold pairState PositiveMatrix.taylor finiteTrial
  rw [Matrix.sum_mulVec]
  have hs := map_sum (WithLp.linearEquiv 2 ℝ (Basis V M N → ℝ))
    (fun k => (pairVector B k : Hilbert V M N)) (Finset.range (L+1))
  change WithLp.ofLp (∑ k ∈ Finset.range (L+1), (pairVector B k : Hilbert V M N)) =
    ∑ k ∈ Finset.range (L+1), WithLp.ofLp (pairVector B k : Hilbert V M N) at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro k _
  simp only [pairVector, WithLp.ofLp_smul, Matrix.smul_mulVec, one_div,
    Matrix.ofLp_toEuclideanLin_apply]
  rfl

/-- The raw Wick normalization is the genuine finite Euclidean squared norm. -/
theorem pairState_dot_self {M N : ℕ}
    (B : Matrix (Mode V) (Mode V) ℝ) (L : ℕ) :
    dotProduct (pairState (M := M) (N := N) B L) (pairState (M := M) (N := N) B L) =
      ‖(finiteTrial B L : Hilbert V M N)‖ ^ 2 := by
  rw [pairState_eq_ofLp_finiteTrial]
  exact PairHomogeneous.dot_self_eq_norm_sq _

end BilayerDressed.FiniteOccupation.TotalCutoff.PairStateBridge

namespace BilayerDressed.CubicPositiveStateNorm
open Matrix BilayerGap FiniteOccupation.TotalCutoff
open PairNorm PositiveMoments PairStateBridge

/-- The actual unsigned finite Wick state has the checked 16-rung norm ceiling. -/
theorem positive16_dot_self_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    dotProduct
      (pairState (M := M) (N := N)
        (CubicSeedChecks.positiveModeKernel 2 2 SeedGraphs.four_by_four_conditions g) 8)
      (pairState (M := M) (N := N)
        (CubicSeedChecks.positiveModeKernel 2 2 SeedGraphs.four_by_four_conditions g) 8) ≤
      (ScalarTrial.M16_0 : ℝ) := by
  rw [pairState_dot_self]
  exact CubicTrialNorm.positive16_norm_sq_le hNM g hg hmax

/-- The actual unsigned finite Wick state has the checked 32-rung norm ceiling. -/
theorem positive32_dot_self_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    dotProduct
      (pairState (M := M) (N := N)
        (CubicSeedChecks.positiveModeKernel 4 2 CubicSeedChecks.eight_by_four_conditions g) 16)
      (pairState (M := M) (N := N)
        (CubicSeedChecks.positiveModeKernel 4 2 CubicSeedChecks.eight_by_four_conditions g) 16) ≤
      (ScalarTrial.M32_0 : ℝ) := by
  rw [pairState_dot_self]
  exact CubicTrialNorm.positive32_norm_sq_le hNM g hg hmax

/-- The actual unsigned finite Wick state has the checked 64-rung norm ceiling. -/
theorem positive64_dot_self_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    dotProduct
      (pairState (M := M) (N := N)
        (CubicSeedChecks.positiveModeKernel 4 4 SeedGraphs.eight_by_eight_conditions g) 32)
      (pairState (M := M) (N := N)
        (CubicSeedChecks.positiveModeKernel 4 4 SeedGraphs.eight_by_eight_conditions g) 32) ≤
      (ScalarTrial.M64_0 : ℝ) := by
  rw [pairState_dot_self]
  exact CubicTrialNorm.positive64_norm_sq_le hNM g hg hmax

end BilayerDressed.CubicPositiveStateNorm

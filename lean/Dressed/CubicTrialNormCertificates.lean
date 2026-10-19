import Dressed.CubicPairNormMajorant
import Dressed.ScalarTrialMajorants

/-!
# Numerical norm certificates for actual cubic trial vectors

These are finite Hilbert norm bounds for the signed trial and the separately
proved positive comparison trial. Homogeneous residual bounds use the actual
vacuum seed norm, not an assumed operator amplification factor.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicTrialNorm
open Matrix BilayerGap FiniteOccupation CubicPairNorm
open TotalCutoff.PairNorm TotalCutoff.PairHomogeneous
set_option maxHeartbeats 3000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma trace16 : traceMajorant 2 2 11597344 = ScalarTrial.T16 := by
  norm_num [traceMajorant, Torus.Vertex, ScalarTrial.T16]
lemma trace32 : traceMajorant 4 2 11548632 = ScalarTrial.T32 := by
  norm_num [traceMajorant, Torus.Vertex, ScalarTrial.T32]
lemma trace64 : traceMajorant 4 4 11499920 = ScalarTrial.T64 := by
  norm_num [traceMajorant, Torus.Vertex, ScalarTrial.T64]

/-- Generic transfer from a checked scalar sum to the actual signed trial. -/
theorem signed_norm_sq_le_of_moment {M N : ℕ} (hNM : N ≤ M)
    (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (L : ℕ) (C : ℚ)
    (hC : ScalarTrial.moment (traceMajorant n m total) L 0 ≤ C) :
    ‖(finiteTrial (modeKernel n m h g) L : Hilbert (Torus.Vertex n m) M N)‖ ^ 2 ≤ (C : ℝ) := by
  apply (actual_finiteTrial_norm_sq_le hNM n m total h hi hc g hg hmax L).trans
  have hh : (∑ k ∈ Finset.range (L+1),
      rationalMajorant coefficientQ (traceMajorant n m total) k) ≤ C := by
    simpa only [ScalarTrial.moment, Nat.choose_zero_right, Nat.cast_one, one_mul] using hC
  exact_mod_cast hh

/-- The positive comparison vector is bounded independently, not equated to the signed vector. -/
theorem positive_norm_sq_le_of_moment {M N : ℕ} (hNM : N ≤ M)
    (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (L : ℕ) (C : ℚ)
    (hC : ScalarTrial.moment (traceMajorant n m total) L 0 ≤ C) :
    ‖(finiteTrial (absoluteModeKernel n m h g) L : Hilbert (Torus.Vertex n m) M N)‖ ^ 2 ≤ (C : ℝ) := by
  apply (actual_absolute_finiteTrial_norm_sq_le hNM n m total h hi hc g hg hmax L).trans
  have hh : (∑ k ∈ Finset.range (L+1),
      rationalMajorant coefficientQ (traceMajorant n m total) k) ≤ C := by
    simpa only [ScalarTrial.moment, Nat.choose_zero_right, Nat.cast_one, one_mul] using hC
  exact_mod_cast hh

/-- Generic checked scalar transfer for actual degree-d homogeneous creation. -/
theorem homogeneous_norm_sq_le_of_moment {M N d : ℕ} (hNM : N ≤ M) (hseed : d ≤ N)
    (n m total : ℕ) (h : SeedGraphs.Conditions n m)
    (hi : SeedGraphs.IncidenceIdentity n m) (hc : CubicSeedChecks.CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex n m) → ℕ) → ℝ) (L : ℕ) (C : ℚ)
    (hC : ScalarTrial.moment (traceMajorant n m total) L d ≤ C) :
    ‖homogeneousAction d r
      (finiteTrial (modeKernel n m h g) L : Hilbert (Torus.Vertex n m) M N)‖ ^ 2 ≤
      ‖homogeneousAction d r
        (TotalCutoff.PairNorm.vacuumVector : Hilbert (Torus.Vertex n m) M N)‖ ^ 2 * (C : ℝ) := by
  apply (actual_homogeneous_finiteTrial_norm_sq_le hNM hseed n m total h hi hc g hg hmax r L).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  change (ScalarTrial.moment (traceMajorant n m total) L d : ℝ) ≤ (C : ℝ)
  exact_mod_cast hC

/-- Actual 16-rung signed finite Taylor norm, through power 8. -/
theorem signed16_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(finiteTrial (modeKernel 2 2 SeedGraphs.four_by_four_conditions g) 8 :
      Hilbert (Torus.Vertex 2 2) M N)‖ ^ 2 ≤ (ScalarTrial.M16_0 : ℝ) := by
  apply signed_norm_sq_le_of_moment hNM 2 2 11597344
    SeedGraphs.four_by_four_conditions SeedGraphs.four_by_four_incidence
    CubicSeedChecks.four_by_four_cubic g hg hmax 8
  rw [trace16]
  exact le_of_lt ScalarTrial.moment16_0

/-- Actual 16-rung positive finite Taylor norm, through power 8. -/
theorem positive16_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(finiteTrial (absoluteModeKernel 2 2 SeedGraphs.four_by_four_conditions g) 8 :
      Hilbert (Torus.Vertex 2 2) M N)‖ ^ 2 ≤ (ScalarTrial.M16_0 : ℝ) := by
  apply positive_norm_sq_le_of_moment hNM 2 2 11597344
    SeedGraphs.four_by_four_conditions SeedGraphs.four_by_four_incidence
    CubicSeedChecks.four_by_four_cubic g hg hmax 8
  rw [trace16]
  exact le_of_lt ScalarTrial.moment16_0

/-- Actual degree-2 homogeneous amplification of the 16-rung signed trial. -/
theorem homogeneous16_2_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hseed : 2 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex 2 2) → ℕ) → ℝ) :
    ‖homogeneousAction 2 r
      (finiteTrial (modeKernel 2 2 SeedGraphs.four_by_four_conditions g) 8 :
        Hilbert (Torus.Vertex 2 2) M N)‖ ^ 2 ≤
      ‖homogeneousAction 2 r
        (TotalCutoff.PairNorm.vacuumVector : Hilbert (Torus.Vertex 2 2) M N)‖ ^ 2 *
        (ScalarTrial.M16_2 : ℝ) := by
  apply homogeneous_norm_sq_le_of_moment hNM hseed 2 2 11597344
    SeedGraphs.four_by_four_conditions SeedGraphs.four_by_four_incidence
    CubicSeedChecks.four_by_four_cubic g hg hmax r 8
  rw [trace16]
  exact le_of_lt ScalarTrial.moment16_2

/-- Actual degree-4 homogeneous amplification of the 16-rung signed trial. -/
theorem homogeneous16_4_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hseed : 4 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex 2 2) → ℕ) → ℝ) :
    ‖homogeneousAction 4 r
      (finiteTrial (modeKernel 2 2 SeedGraphs.four_by_four_conditions g) 8 :
        Hilbert (Torus.Vertex 2 2) M N)‖ ^ 2 ≤
      ‖homogeneousAction 4 r
        (TotalCutoff.PairNorm.vacuumVector : Hilbert (Torus.Vertex 2 2) M N)‖ ^ 2 *
        (ScalarTrial.M16_4 : ℝ) := by
  apply homogeneous_norm_sq_le_of_moment hNM hseed 2 2 11597344
    SeedGraphs.four_by_four_conditions SeedGraphs.four_by_four_incidence
    CubicSeedChecks.four_by_four_cubic g hg hmax r 8
  rw [trace16]
  exact le_of_lt ScalarTrial.moment16_4

/-- Actual degree-6 homogeneous amplification of the 16-rung signed trial. -/
theorem homogeneous16_6_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hseed : 6 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex 2 2) → ℕ) → ℝ) :
    ‖homogeneousAction 6 r
      (finiteTrial (modeKernel 2 2 SeedGraphs.four_by_four_conditions g) 8 :
        Hilbert (Torus.Vertex 2 2) M N)‖ ^ 2 ≤
      ‖homogeneousAction 6 r
        (TotalCutoff.PairNorm.vacuumVector : Hilbert (Torus.Vertex 2 2) M N)‖ ^ 2 *
        (ScalarTrial.M16_6 : ℝ) := by
  apply homogeneous_norm_sq_le_of_moment hNM hseed 2 2 11597344
    SeedGraphs.four_by_four_conditions SeedGraphs.four_by_four_incidence
    CubicSeedChecks.four_by_four_cubic g hg hmax r 8
  rw [trace16]
  exact le_of_lt ScalarTrial.moment16_6

/-- Actual 32-rung signed finite Taylor norm, through power 16. -/
theorem signed32_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(finiteTrial (modeKernel 4 2 CubicSeedChecks.eight_by_four_conditions g) 16 :
      Hilbert (Torus.Vertex 4 2) M N)‖ ^ 2 ≤ (ScalarTrial.M32_0 : ℝ) := by
  apply signed_norm_sq_le_of_moment hNM 4 2 11548632
    CubicSeedChecks.eight_by_four_conditions CubicSeedChecks.eight_by_four_incidence
    CubicSeedChecks.eight_by_four_cubic g hg hmax 16
  rw [trace32]
  exact le_of_lt ScalarTrial.moment32_0

/-- Actual 32-rung positive finite Taylor norm, through power 16. -/
theorem positive32_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(finiteTrial (absoluteModeKernel 4 2 CubicSeedChecks.eight_by_four_conditions g) 16 :
      Hilbert (Torus.Vertex 4 2) M N)‖ ^ 2 ≤ (ScalarTrial.M32_0 : ℝ) := by
  apply positive_norm_sq_le_of_moment hNM 4 2 11548632
    CubicSeedChecks.eight_by_four_conditions CubicSeedChecks.eight_by_four_incidence
    CubicSeedChecks.eight_by_four_cubic g hg hmax 16
  rw [trace32]
  exact le_of_lt ScalarTrial.moment32_0

/-- Actual degree-2 homogeneous amplification of the 32-rung signed trial. -/
theorem homogeneous32_2_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hseed : 2 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex 4 2) → ℕ) → ℝ) :
    ‖homogeneousAction 2 r
      (finiteTrial (modeKernel 4 2 CubicSeedChecks.eight_by_four_conditions g) 16 :
        Hilbert (Torus.Vertex 4 2) M N)‖ ^ 2 ≤
      ‖homogeneousAction 2 r
        (TotalCutoff.PairNorm.vacuumVector : Hilbert (Torus.Vertex 4 2) M N)‖ ^ 2 *
        (ScalarTrial.M32_2 : ℝ) := by
  apply homogeneous_norm_sq_le_of_moment hNM hseed 4 2 11548632
    CubicSeedChecks.eight_by_four_conditions CubicSeedChecks.eight_by_four_incidence
    CubicSeedChecks.eight_by_four_cubic g hg hmax r 16
  rw [trace32]
  exact le_of_lt ScalarTrial.moment32_2

/-- Actual degree-4 homogeneous amplification of the 32-rung signed trial. -/
theorem homogeneous32_4_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hseed : 4 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex 4 2) → ℕ) → ℝ) :
    ‖homogeneousAction 4 r
      (finiteTrial (modeKernel 4 2 CubicSeedChecks.eight_by_four_conditions g) 16 :
        Hilbert (Torus.Vertex 4 2) M N)‖ ^ 2 ≤
      ‖homogeneousAction 4 r
        (TotalCutoff.PairNorm.vacuumVector : Hilbert (Torus.Vertex 4 2) M N)‖ ^ 2 *
        (ScalarTrial.M32_4 : ℝ) := by
  apply homogeneous_norm_sq_le_of_moment hNM hseed 4 2 11548632
    CubicSeedChecks.eight_by_four_conditions CubicSeedChecks.eight_by_four_incidence
    CubicSeedChecks.eight_by_four_cubic g hg hmax r 16
  rw [trace32]
  exact le_of_lt ScalarTrial.moment32_4

/-- Actual degree-6 homogeneous amplification of the 32-rung signed trial. -/
theorem homogeneous32_6_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hseed : 6 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex 4 2) → ℕ) → ℝ) :
    ‖homogeneousAction 6 r
      (finiteTrial (modeKernel 4 2 CubicSeedChecks.eight_by_four_conditions g) 16 :
        Hilbert (Torus.Vertex 4 2) M N)‖ ^ 2 ≤
      ‖homogeneousAction 6 r
        (TotalCutoff.PairNorm.vacuumVector : Hilbert (Torus.Vertex 4 2) M N)‖ ^ 2 *
        (ScalarTrial.M32_6 : ℝ) := by
  apply homogeneous_norm_sq_le_of_moment hNM hseed 4 2 11548632
    CubicSeedChecks.eight_by_four_conditions CubicSeedChecks.eight_by_four_incidence
    CubicSeedChecks.eight_by_four_cubic g hg hmax r 16
  rw [trace32]
  exact le_of_lt ScalarTrial.moment32_6

/-- Actual 64-rung signed finite Taylor norm, through power 32. -/
theorem signed64_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(finiteTrial (modeKernel 4 4 SeedGraphs.eight_by_eight_conditions g) 32 :
      Hilbert (Torus.Vertex 4 4) M N)‖ ^ 2 ≤ (ScalarTrial.M64_0 : ℝ) := by
  apply signed_norm_sq_le_of_moment hNM 4 4 11499920
    SeedGraphs.eight_by_eight_conditions SeedGraphs.eight_by_eight_incidence
    CubicSeedChecks.eight_by_eight_cubic g hg hmax 32
  rw [trace64]
  exact le_of_lt ScalarTrial.moment64_0

/-- Actual 64-rung positive finite Taylor norm, through power 32. -/
theorem positive64_norm_sq_le {M N : ℕ} (hNM : N ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    ‖(finiteTrial (absoluteModeKernel 4 4 SeedGraphs.eight_by_eight_conditions g) 32 :
      Hilbert (Torus.Vertex 4 4) M N)‖ ^ 2 ≤ (ScalarTrial.M64_0 : ℝ) := by
  apply positive_norm_sq_le_of_moment hNM 4 4 11499920
    SeedGraphs.eight_by_eight_conditions SeedGraphs.eight_by_eight_incidence
    CubicSeedChecks.eight_by_eight_cubic g hg hmax 32
  rw [trace64]
  exact le_of_lt ScalarTrial.moment64_0

/-- Actual degree-2 homogeneous amplification of the 64-rung signed trial. -/
theorem homogeneous64_2_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hseed : 2 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex 4 4) → ℕ) → ℝ) :
    ‖homogeneousAction 2 r
      (finiteTrial (modeKernel 4 4 SeedGraphs.eight_by_eight_conditions g) 32 :
        Hilbert (Torus.Vertex 4 4) M N)‖ ^ 2 ≤
      ‖homogeneousAction 2 r
        (TotalCutoff.PairNorm.vacuumVector : Hilbert (Torus.Vertex 4 4) M N)‖ ^ 2 *
        (ScalarTrial.M64_2 : ℝ) := by
  apply homogeneous_norm_sq_le_of_moment hNM hseed 4 4 11499920
    SeedGraphs.eight_by_eight_conditions SeedGraphs.eight_by_eight_incidence
    CubicSeedChecks.eight_by_eight_cubic g hg hmax r 32
  rw [trace64]
  exact le_of_lt ScalarTrial.moment64_2

/-- Actual degree-4 homogeneous amplification of the 64-rung signed trial. -/
theorem homogeneous64_4_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hseed : 4 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex 4 4) → ℕ) → ℝ) :
    ‖homogeneousAction 4 r
      (finiteTrial (modeKernel 4 4 SeedGraphs.eight_by_eight_conditions g) 32 :
        Hilbert (Torus.Vertex 4 4) M N)‖ ^ 2 ≤
      ‖homogeneousAction 4 r
        (TotalCutoff.PairNorm.vacuumVector : Hilbert (Torus.Vertex 4 4) M N)‖ ^ 2 *
        (ScalarTrial.M64_4 : ℝ) := by
  apply homogeneous_norm_sq_le_of_moment hNM hseed 4 4 11499920
    SeedGraphs.eight_by_eight_conditions SeedGraphs.eight_by_eight_incidence
    CubicSeedChecks.eight_by_eight_cubic g hg hmax r 32
  rw [trace64]
  exact le_of_lt ScalarTrial.moment64_4

/-- Actual degree-6 homogeneous amplification of the 64-rung signed trial. -/
theorem homogeneous64_6_norm_sq_le {M N : ℕ} (hNM : N ≤ M) (hseed : 6 ≤ N)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (r : (Mode (Torus.Vertex 4 4) → ℕ) → ℝ) :
    ‖homogeneousAction 6 r
      (finiteTrial (modeKernel 4 4 SeedGraphs.eight_by_eight_conditions g) 32 :
        Hilbert (Torus.Vertex 4 4) M N)‖ ^ 2 ≤
      ‖homogeneousAction 6 r
        (TotalCutoff.PairNorm.vacuumVector : Hilbert (Torus.Vertex 4 4) M N)‖ ^ 2 *
        (ScalarTrial.M64_6 : ℝ) := by
  apply homogeneous_norm_sq_le_of_moment hNM hseed 4 4 11499920
    SeedGraphs.eight_by_eight_conditions SeedGraphs.eight_by_eight_incidence
    CubicSeedChecks.eight_by_eight_cubic g hg hmax r 32
  rw [trace64]
  exact le_of_lt ScalarTrial.moment64_6

end BilayerDressed.CubicTrialNorm

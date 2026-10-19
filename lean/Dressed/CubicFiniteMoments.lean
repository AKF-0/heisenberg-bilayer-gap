import Dressed.FiniteWickPairings
import Dressed.CubicSeedSupersolution

/-! Actual finite positive trial moments for the three cubic seed graphs.
All kernel row and covariance conditions are discharged for 0 ≤ g ≤ 1/10.
This is not yet the signed hard-core residual expectation or final gap assembly.
-/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicSeedChecks
open BilayerGap SeedGraphs FiniteOccupation.TotalCutoff.PositiveMoments
open CubicWick.FourRegularData

/-- The actual mode kernel, including all three independent Cartesian colors. -/
def positiveModeKernel (n m : ℕ) (h : Conditions n m) (g : ℝ) :=
  FiniteWick.colorLift (χ := Fin 3) (positiveKernel n m h g)

def modeCovariance (n m total : ℕ) (h : Conditions n m) (g : ℝ) :=
  FiniteWick.colorLift (χ := Fin 3)
    (FiniteWick.covarianceMajorant (positiveKernel n m h g) (tau total))

/-- This proposition contains a concrete finite vector, not an abstract moment sequence. -/
def SeedMomentBound (n m total : ℕ) (h : Conditions n m)
    (M N k : ℕ) (g : ℝ) : Prop :=
  let B := positiveModeKernel n m h g
  let L := modeCovariance n m total h g
  let ψ := pairState (M := M) (N := N) B k
  ∀ l,PositiveMatrix.expect ψ (PositiveMatrix.word FiniteOccupation.TotalCutoff.create l)≤
    dotProduct ψ ψ*FiniteWickPairings.wick L l

/-- All operator and covariance premises are proved from the actual graph. -/
theorem actual_seed_moments (n m total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    (M N k : ℕ) (hNM : N≤M) (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    SeedMomentBound n m total h M N k g := by
  have hB (u v : Torus.Vertex n m×Fin 3) : 0≤positiveModeKernel n m h g u v := by
    unfold positiveModeKernel FiniteWick.colorLift positiveKernel
    split_ifs <;> positivity
  have hsym (u v : Torus.Vertex n m×Fin 3) :
      positiveModeKernel n m h g u v=positiveModeKernel n m h g v u := by
    unfold positiveModeKernel FiniteWick.colorLift positiveKernel
    by_cases he : u.2=v.2
    · simp only [he,eq_self_iff_true,if_true]
      rw [cubicKernel_symmetric]
    · simp [he,Ne.symm he]
  have htau : 0≤tau total := by
    unfold tau
    exact div_nonneg (by positivity) (by norm_num)
  have hL (u v : Torus.Vertex n m×Fin 3) : 0≤ modeCovariance n m total h g u v := by
    unfold modeCovariance FiniteWick.colorLift FiniteWick.covarianceMajorant positiveKernel
    split_ifs
    · exact add_nonneg (abs_nonneg _) htau
    · norm_num
  exact pairState_wick_bound hNM (positiveModeKernel n m h g) (modeCovariance n m total h g)
    hB hsym hL ((493/4000 : ℝ)^2) (by norm_num)
    (FiniteWick.square_row_le _ (493/4000) hB (by norm_num)
      (actual_three_color_row_bound n m total h hi hc g hg hmax))
    (actual_three_color_supersolution n m total h hi hc g hg hmax) k

/-- Ordinary 4×4 seed, with every finite kernel premise discharged. -/
theorem four_by_four_moments (M N k : ℕ) (hNM : N≤M)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    SeedMomentBound 2 2 11597344 four_by_four_conditions M N k g :=
  actual_seed_moments 2 2 11597344 four_by_four_conditions four_by_four_incidence
    four_by_four_cubic M N k hNM g hg hmax

/-- Ordinary 8×4 seed, with every finite kernel premise discharged. -/
theorem eight_by_four_moments (M N k : ℕ) (hNM : N≤M)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    SeedMomentBound 4 2 11548632 eight_by_four_conditions M N k g :=
  actual_seed_moments 4 2 11548632 eight_by_four_conditions eight_by_four_incidence
    eight_by_four_cubic M N k hNM g hg hmax

/-- Ordinary 8×8 seed, with every finite kernel premise discharged. -/
theorem eight_by_eight_moments (M N k : ℕ) (hNM : N≤M)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    SeedMomentBound 4 4 11499920 eight_by_eight_conditions M N k g :=
  actual_seed_moments 4 4 11499920 eight_by_eight_conditions eight_by_eight_incidence
    eight_by_eight_cubic M N k hNM g hg hmax

end BilayerDressed.CubicSeedChecks

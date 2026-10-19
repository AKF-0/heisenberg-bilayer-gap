import Dressed.FinitePhysicalWick

/-! Signed physical cubic trial expectations with every covariance and
normalization premise discharged on the three ordinary seed rectangles.
The remaining input is an explicit finite creation-polynomial coefficient sum.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicPhysicalMeans
open Matrix BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open FiniteOccupation FiniteOccupation.TotalCutoff.PositiveMoments
open FinitePhysicalWick

 theorem absolute_modeKernel (n m : ℕ) (h : Conditions n m) (g : ℝ) :
    PositiveMatrix.entryAbs (FiniteDressed.modeKernel (cubicKernel (graph n m h) g))=
      positiveModeKernel n m h g := by
  ext i j
  simp only [PositiveMatrix.entryAbs,FiniteDressed.modeKernel,positiveModeKernel,
    FiniteWick.colorLift,positiveKernel]
  split_ifs <;> simp

 theorem covariance_nonneg (n m total : ℕ) (h : Conditions n m) (g : ℝ)
    (i j : Mode (Torus.Vertex n m)) : 0 ≤ modeCovariance n m total h g i j := by
  have ht : 0 ≤ tau total := by
    unfold tau
    exact div_nonneg (by positivity) (by norm_num)
  unfold modeCovariance FiniteWick.colorLift FiniteWick.covarianceMajorant positiveKernel
  split_ifs
  · exact add_nonneg (abs_nonneg _) ht
  · norm_num

/-- Finite pairing polynomials are monotone on nonnegative covariance entries. -/
theorem wick_mono {ι : Type*} (L L' : ι→ι→ℝ)
    (hL : ∀ i j,0 ≤ L i j) (hle : ∀ i j,L i j ≤ L' i j) (w : List ι) :
    FiniteWickPairings.wick L w ≤ FiniteWickPairings.wick L' w := by
  have hh := FiniteWickPairings.dominates L' (fun i j => (hL i j).trans (hle i j))
    (FiniteWickPairings.wick L) (fun i l => by
      rw [FiniteWickPairings.wick]
      exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hle i l[a])
        (FiniteWickPairings.wick_nonneg L hL _)) w
  simpa only [FiniteWickPairings.wick_nil,one_mul] using hh

/-- The absolute cubic kernel and its covariance are bounded by the endpoint. -/
theorem covariance_le_endpoint (n m total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (i j : Mode (Torus.Vertex n m)) :
    modeCovariance n m total h g i j ≤ modeCovariance n m total h (1/10) i j := by
  unfold modeCovariance FiniteWick.colorLift FiniteWick.covarianceMajorant positiveKernel
  split_ifs
  · apply add_le_add_right
    rw [cubicKernel_abs _ (graph_signs n m total h hi hc) g hg,
      cubicKernel_abs _ (graph_signs n m total h hi hc) (1/10) (by norm_num)]
    exact cubicEnvelope_monotone _ (graph_signs n m total h hi hc) _ _ hg hmax _ _
  · exact le_rfl

 theorem coefficient_sum_le_endpoint (n m total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ) (w : α→List (Mode (Torus.Vertex n m))) :
    (∑ a, |c a| * FiniteWickPairings.wick (modeCovariance n m total h g) (w a)) ≤
      ∑ a, |c a| * FiniteWickPairings.wick (modeCovariance n m total h (1/10)) (w a) := by
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
    (wick_mono _ _ (covariance_nonneg n m total h g)
      (covariance_le_endpoint n m total h hi hc g hg hmax) (w a)) (abs_nonneg _)

/-- Actual signed hard-core polynomial mean, using its own positive majorant state. -/
theorem actual_seed_physical_mean (n m total : ℕ) (h : Conditions n m)
    (hi : IncidenceIdentity n m) (hc : CubicConditions n m total)
    {M : ℕ} (hM : 2 ≤ M) (hAM : Fintype.card (Torus.Vertex n m) ≤ M)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ) (w : α→List (Mode (Torus.Vertex n m))) :
    |⟪dressedVector (cubicKernel (graph n m h) g),
        (physicalPolynomial c w).toEuclideanLin
          (dressedVector (cubicKernel (graph n m h) g))⟫| ≤
      dotProduct
        (pairState (M := M) (N := Fintype.card (Torus.Vertex n m))
          (positiveModeKernel n m h g) (Fintype.card (Torus.Vertex n m)/2))
        (pairState (M := M) (N := Fintype.card (Torus.Vertex n m))
          (positiveModeKernel n m h g) (Fintype.card (Torus.Vertex n m)/2)) *
      ∑ a, |c a| * FiniteWickPairings.wick (modeCovariance n m total h g) (w a) := by
  have hB (i j : Mode (Torus.Vertex n m)) : 0 ≤ positiveModeKernel n m h g i j := by
    unfold positiveModeKernel FiniteWick.colorLift positiveKernel
    split_ifs <;> positivity
  have hr := FiniteWick.square_row_le (positiveModeKernel n m h g) (493/4000)
    hB (by norm_num) (actual_three_color_row_bound n m total h hi hc g hg hmax)
  have hs := actual_three_color_supersolution n m total h hi hc g hg hmax
  have hb := physical_polynomial_mean_bound hM hAM (cubicKernel (graph n m h) g)
    (cubicKernel_symmetric (graph n m h) g) (modeCovariance n m total h g)
    (covariance_nonneg n m total h g) ((493/4000 : ℝ)^2) (by norm_num)
    (by simpa only [absolute_modeKernel] using hr)
    (by
      change ∀ i j, PositiveMatrix.entryAbs (FiniteDressed.modeKernel
        (cubicKernel (graph n m h) g)) i j + _ ≤ _
      rw [absolute_modeKernel]
      exact hs) c w
  simpa only [absolute_modeKernel] using hb


/-- The actual 4×4 physical polynomial mean, with no covariance or norm premise. -/
theorem four_by_four_physical_mean
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ)
    (w : α→List (Mode (Torus.Vertex 2 2))) :
    |⟪dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g),
        (physicalPolynomial c w).toEuclideanLin
          (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M16_0 : ℝ) *
        ∑ a, |c a| * FiniteWickPairings.wick
          (modeCovariance 2 2 11597344 four_by_four_conditions g) (w a) := by
  have hb := actual_seed_physical_mean 2 2 11597344 four_by_four_conditions
    four_by_four_incidence four_by_four_cubic (M := 16) (by norm_num)
    (by norm_num [Torus.Vertex]) g hg hmax c w
  have hn := CubicPositiveStateNorm.positive16_dot_self_le (M := 16) (N := 16)
    (by omega) g hg hmax
  have hsum : 0 ≤ ∑ a, |c a| * FiniteWickPairings.wick
      (modeCovariance 2 2 11597344 four_by_four_conditions g) (w a) := by
    exact Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _)
      (FiniteWickPairings.wick_nonneg _ (covariance_nonneg _ _ _ _ _) _)
  norm_num [Torus.Vertex] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hn hsum)

/-- The actual 8×4 physical polynomial mean, with no covariance or norm premise. -/
theorem eight_by_four_physical_mean
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ)
    (w : α→List (Mode (Torus.Vertex 4 2))) :
    |⟪dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g),
        (physicalPolynomial c w).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M32_0 : ℝ) *
        ∑ a, |c a| * FiniteWickPairings.wick
          (modeCovariance 4 2 11548632 eight_by_four_conditions g) (w a) := by
  have hb := actual_seed_physical_mean 4 2 11548632 eight_by_four_conditions
    eight_by_four_incidence eight_by_four_cubic (M := 32) (by norm_num)
    (by norm_num [Torus.Vertex]) g hg hmax c w
  have hn := CubicPositiveStateNorm.positive32_dot_self_le (M := 32) (N := 32)
    (by omega) g hg hmax
  have hsum : 0 ≤ ∑ a, |c a| * FiniteWickPairings.wick
      (modeCovariance 4 2 11548632 eight_by_four_conditions g) (w a) := by
    exact Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _)
      (FiniteWickPairings.wick_nonneg _ (covariance_nonneg _ _ _ _ _) _)
  norm_num [Torus.Vertex] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hn hsum)

/-- The actual 8×8 physical polynomial mean, with no covariance or norm premise. -/
theorem eight_by_eight_physical_mean
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ)
    (w : α→List (Mode (Torus.Vertex 4 4))) :
    |⟪dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g),
        (physicalPolynomial c w).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g))⟫| ≤
      (ScalarTrial.M64_0 : ℝ) *
        ∑ a, |c a| * FiniteWickPairings.wick
          (modeCovariance 4 4 11499920 eight_by_eight_conditions g) (w a) := by
  have hb := actual_seed_physical_mean 4 4 11499920 eight_by_eight_conditions
    eight_by_eight_incidence eight_by_eight_cubic (M := 64) (by norm_num)
    (by norm_num [Torus.Vertex]) g hg hmax c w
  have hn := CubicPositiveStateNorm.positive64_dot_self_le (M := 64) (N := 64)
    (by omega) g hg hmax
  have hsum : 0 ≤ ∑ a, |c a| * FiniteWickPairings.wick
      (modeCovariance 4 4 11499920 eight_by_eight_conditions g) (w a) := by
    exact Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _)
      (FiniteWickPairings.wick_nonneg _ (covariance_nonneg _ _ _ _ _) _)
  norm_num [Torus.Vertex] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hn hsum)

end BilayerDressed.CubicPhysicalMeans

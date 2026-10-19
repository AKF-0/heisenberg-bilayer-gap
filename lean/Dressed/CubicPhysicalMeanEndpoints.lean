import Dressed.CubicPhysicalMeans

/-! Endpoint-covariance interfaces for literal signed physical polynomials.
Only the explicit finite coefficient sum remains a premise; separate coefficient
certificates must discharge it for the actual global residual polynomial.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicPhysicalMeans
open Matrix BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open FiniteOccupation FinitePhysicalWick

/-- Physical 4×4 expectation at g with the fixed g=.1 covariance. -/
theorem four_by_four_physical_mean_endpoint
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ)
    (w : α→List (Mode (Torus.Vertex 2 2))) :
    |⟪dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g),
        (physicalPolynomial c w).toEuclideanLin
          (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M16_0 : ℝ) *
        ∑ a, |c a| * FiniteWickPairings.wick
          (modeCovariance 2 2 11597344 four_by_four_conditions (1/10)) (w a) := by
  exact (four_by_four_physical_mean g hg hmax c w).trans
    (mul_le_mul_of_nonneg_left
      (coefficient_sum_le_endpoint 2 2 11597344 four_by_four_conditions
        four_by_four_incidence four_by_four_cubic g hg hmax c w)
      (by norm_num [ScalarTrial.M16_0]))

/-- Conditional only on a literal finite coefficient sum, not a state or moment oracle. -/
theorem four_by_four_physical_mean_of_coefficients
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ)
    (w : α→List (Mode (Torus.Vertex 2 2)))
    (hcoef : (∑ a, |c a| * FiniteWickPairings.wick
      (modeCovariance 2 2 11597344 four_by_four_conditions (1/10)) (w a)) ≤
        (ScalarTrial.meanCoefficient16 : ℝ)) :
    |⟪dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g),
        (physicalPolynomial c w).toEuclideanLin
          (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g))⟫| < 167/1000000 := by
  apply lt_of_le_of_lt (four_by_four_physical_mean_endpoint g hg hmax c w)
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcoef
    (by norm_num [ScalarTrial.M16_0]))
  norm_num [ScalarTrial.M16_0,ScalarTrial.meanCoefficient16]

/-- Physical 8×4 expectation at g with the fixed g=.1 covariance. -/
theorem eight_by_four_physical_mean_endpoint
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ)
    (w : α→List (Mode (Torus.Vertex 4 2))) :
    |⟪dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g),
        (physicalPolynomial c w).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M32_0 : ℝ) *
        ∑ a, |c a| * FiniteWickPairings.wick
          (modeCovariance 4 2 11548632 eight_by_four_conditions (1/10)) (w a) := by
  exact (eight_by_four_physical_mean g hg hmax c w).trans
    (mul_le_mul_of_nonneg_left
      (coefficient_sum_le_endpoint 4 2 11548632 eight_by_four_conditions
        eight_by_four_incidence eight_by_four_cubic g hg hmax c w)
      (by norm_num [ScalarTrial.M32_0]))

/-- Conditional only on a literal finite coefficient sum, not a state or moment oracle. -/
theorem eight_by_four_physical_mean_of_coefficients
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ)
    (w : α→List (Mode (Torus.Vertex 4 2)))
    (hcoef : (∑ a, |c a| * FiniteWickPairings.wick
      (modeCovariance 4 2 11548632 eight_by_four_conditions (1/10)) (w a)) ≤
        (ScalarTrial.meanCoefficient32 : ℝ)) :
    |⟪dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g),
        (physicalPolynomial c w).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g))⟫| < 173/500000 := by
  apply lt_of_le_of_lt (eight_by_four_physical_mean_endpoint g hg hmax c w)
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcoef
    (by norm_num [ScalarTrial.M32_0]))
  norm_num [ScalarTrial.M32_0,ScalarTrial.meanCoefficient32]

/-- Physical 8×8 expectation at g with the fixed g=.1 covariance. -/
theorem eight_by_eight_physical_mean_endpoint
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ)
    (w : α→List (Mode (Torus.Vertex 4 4))) :
    |⟪dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g),
        (physicalPolynomial c w).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g))⟫| ≤
      (ScalarTrial.M64_0 : ℝ) *
        ∑ a, |c a| * FiniteWickPairings.wick
          (modeCovariance 4 4 11499920 eight_by_eight_conditions (1/10)) (w a) := by
  exact (eight_by_eight_physical_mean g hg hmax c w).trans
    (mul_le_mul_of_nonneg_left
      (coefficient_sum_le_endpoint 4 4 11499920 eight_by_eight_conditions
        eight_by_eight_incidence eight_by_eight_cubic g hg hmax c w)
      (by norm_num [ScalarTrial.M64_0]))

/-- Conditional only on a literal finite coefficient sum, not a state or moment oracle. -/
theorem eight_by_eight_physical_mean_of_coefficients
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    {α : Type*} [Fintype α] (c : α→ℝ)
    (w : α→List (Mode (Torus.Vertex 4 4)))
    (hcoef : (∑ a, |c a| * FiniteWickPairings.wick
      (modeCovariance 4 4 11499920 eight_by_eight_conditions (1/10)) (w a)) ≤
        (ScalarTrial.meanCoefficient64 : ℝ)) :
    |⟪dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g),
        (physicalPolynomial c w).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g))⟫| < 1/1250 := by
  apply lt_of_le_of_lt (eight_by_eight_physical_mean_endpoint g hg hmax c w)
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcoef
    (by norm_num [ScalarTrial.M64_0]))
  norm_num [ScalarTrial.M64_0,ScalarTrial.meanCoefficient64]

end BilayerDressed.CubicPhysicalMeans

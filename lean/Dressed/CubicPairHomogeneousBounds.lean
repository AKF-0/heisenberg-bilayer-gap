import Dressed.CubicPairHomogeneous
import Dressed.CubicResidualIntervalBounds

/-! Actual homogeneous bosonic vacuum certificates for the two Temple seeds.
All physical and finite-occupation identifications precede the scalar bound. -/
noncomputable section
open scoped RealInnerProductSpace
namespace BilayerDressed.CubicPairHomogeneous
open BilayerGap FiniteOccupation TotalCutoff SeedGraphs CubicSeedChecks
open CubicResidualIntervalBounds

theorem residual_vacuum_norm_sq_bound16 {M N : ℕ} (hNM : N≤M) (hN : 2≤N)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ‖(Homogeneous.homogeneousOperator (M := M) (N := N) 2
      (residualCoefficients (graph 2 2 four_by_four_conditions) g)).toEuclideanLin
      PairNorm.vacuumVector‖^2≤(ScalarTrial.F16_2 : ℝ) := by
  rw [residual_vacuum_norm_eq_physical hNM hN 2 2
    four_by_four_conditions four_by_four_incidence]
  rw [←CubicResidualPolynomial.coe_residual2_eq_physicalPairResidual 2 2
    four_by_four_conditions four_by_four_incidence]
  exact physical_residual2_norm_sq_bound16 g hg hmax

theorem residual_vacuum_norm_sq_bound32 {M N : ℕ} (hNM : N≤M) (hN : 2≤N)
    (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    ‖(Homogeneous.homogeneousOperator (M := M) (N := N) 2
      (residualCoefficients (graph 4 2 eight_by_four_conditions) g)).toEuclideanLin
      PairNorm.vacuumVector‖^2≤(ScalarTrial.F32_2 : ℝ) := by
  rw [residual_vacuum_norm_eq_physical hNM hN 4 2
    eight_by_four_conditions eight_by_four_incidence]
  rw [←CubicResidualPolynomial.coe_residual2_eq_physicalPairResidual 4 2
    eight_by_four_conditions eight_by_four_incidence]
  exact physical_residual2_norm_sq_bound32 g hg hmax

end BilayerDressed.CubicPairHomogeneous

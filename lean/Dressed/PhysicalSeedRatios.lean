import Dressed.GroundShiftPartition
import Dressed.PhysicalWarmupCriterion
import Dressed.ScalarSeedExponentialBounds
import Dressed.PhysicalGramLowerBound

/-! Genuine physical coordinate seeds from the two correlated ground-energy
bounds and three ground-subtracted finite partition estimates. None of these
finite inputs is asserted merely from scalar certificates. -/
noncomputable section
namespace BilayerDressed.PhysicalSeeds
open BilayerGap
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-- The five concrete finite energy/thermal inputs imply the exact initial
coordinate triple used in all six ordered warmups. -/
theorem coordinate_bounds_of_energy_thermal (g : ℝ)
    (hdx : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g)-
      2*groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) ≤ (ScalarWarmup.dx:ℝ))
    (hdy : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 8 g)-
      2*groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g) ≤ (ScalarWarmup.dy:ℝ))
    (hQ0 : relativePartition (PhysicalGram.fullHamiltonian_hermitian 4 4 g) 16 ≤ (ScalarWarmup.Q0:ℝ))
    (hQ1 : relativePartition (PhysicalGram.fullHamiltonian_hermitian 8 4 g) 16 ≤ (ScalarWarmup.Q1:ℝ))
    (hQ2 : relativePartition (PhysicalGram.fullHamiltonian_hermitian 8 8 g) 16 ≤ (ScalarWarmup.Q2:ℝ)) :
    CoordinateWarmup.Bounds (BilayerModel.family g).spectral.partition ⟨4,4,16⟩
      ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0 := by
  have hx := partition_spatial_ratio_lower
    (PhysicalGram.fullHamiltonian_hermitian 4 4 g)
    (PhysicalGram.fullHamiltonian_hermitian 8 4 g) 16 _ _ (by norm_num) hdx hQ0
  have hy := partition_spatial_ratio_lower
    (PhysicalGram.fullHamiltonian_hermitian 8 4 g)
    (PhysicalGram.fullHamiltonian_hermitian 8 8 g) 16 _ _ (by norm_num) hdy hQ1
  have ht := partition_thermal_ratio_lower
    (PhysicalGram.fullHamiltonian_hermitian 8 8 g) 16 _ hQ2
  have ha := ScalarThermal.initial_a_exponential
  have hb := ScalarThermal.initial_b_exponential
  have hc : 1-1/(ScalarWarmup.Q2:ℝ)^2 < (ScalarWarmup.c0:ℝ) := by
    exact_mod_cast ScalarWarmup.initial_c
  unfold CoordinateWarmup.Bounds staircaseA staircaseB staircaseC partitionRatio
  simp only [BilayerModel.family_partition]
  norm_num only [doubleCoord, BilayerModel.partition, BilayerModel.hamiltonian]
  change 1-TraceConvexity.partition (Torus.fullHamiltonian 8 4 RealRungOperators.h RealRungOperators.G g) 16 /
      (TraceConvexity.partition (Torus.fullHamiltonian 4 4 RealRungOperators.h RealRungOperators.G g) 16)^2 ≤ _ ∧
    1-TraceConvexity.partition (Torus.fullHamiltonian 8 8 RealRungOperators.h RealRungOperators.G g) 16 /
      (TraceConvexity.partition (Torus.fullHamiltonian 8 4 RealRungOperators.h RealRungOperators.G g) 16)^2 ≤ _ ∧
    1-TraceConvexity.partition (Torus.fullHamiltonian 8 8 RealRungOperators.h RealRungOperators.G g) 32 /
      (TraceConvexity.partition (Torus.fullHamiltonian 8 8 RealRungOperators.h RealRungOperators.G g) 16)^2 ≤ _
  push_cast at ha hb
  simp only [neg_mul] at hx hy
  norm_num only [show (2:ℝ)*16=32 by norm_num] at ht
  exact ⟨by linarith only [hx,ha],by linarith only [hy,hb],by linarith only [ht,hc]⟩

/-- This is a conditional physical all-size theorem, not a claim that the five
finite inputs have already been discharged by the cubic coefficient checks. -/
theorem uniform_gap_of_energy_thermal {g : ℝ} (hg : 0 ≤ g)
    (hdx : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g)-
      2*groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) ≤ (ScalarWarmup.dx:ℝ))
    (hdy : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 8 g)-
      2*groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g) ≤ (ScalarWarmup.dy:ℝ))
    (hQ0 : relativePartition (PhysicalGram.fullHamiltonian_hermitian 4 4 g) 16 ≤ (ScalarWarmup.Q0:ℝ))
    (hQ1 : relativePartition (PhysicalGram.fullHamiltonian_hermitian 8 4 g) 16 ≤ (ScalarWarmup.Q1:ℝ))
    (hQ2 : relativePartition (PhysicalGram.fullHamiltonian_hermitian 8 8 g) 16 ≤ (ScalarWarmup.Q2:ℝ))
    (L : ℕ) (hL : ValidSize L) (hlarge : 256 ≤ L)
    (i k : Fin ((BilayerModel.family g).dim L L : ℕ)) (hik : i ≠ k)
    (hground : ∀ j,((BilayerModel.family g).hermitian L L).eigenvalues i ≤
      ((BilayerModel.family g).hermitian L L).eigenvalues j) :
    PhysicalWarmup.gapLowerBound < ((BilayerModel.family g).hermitian L L).eigenvalues k-
      ((BilayerModel.family g).hermitian L L).eigenvalues i :=
  PhysicalWarmup.uniform_gap_of_seed hg (coordinate_bounds_of_energy_thermal g hdx hdy hQ0 hQ1 hQ2)
    L hL hlarge i k hik hground

end BilayerDressed.PhysicalSeeds

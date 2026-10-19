import Dressed.GeometricThermalBound
import Dressed.ScalarIntervalBounds
import Dressed.ScalarSeedExponentialBounds

/-! Actual three finite-volume thermal ceilings at beta=16, conditional only
on the three displayed genuine ground-energy upper bounds. -/
noncomputable section
namespace BilayerDressed.CubicSeedThermal
open BilayerGap ScalarInterval ScalarThermal

theorem thermal16 {g : ℝ} (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) ≤ shift16 g+167/1000000) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian 4 4 g) 16 ≤ (ScalarWarmup.Q0:ℝ) := by
  have hden := denominator16_lower hg hgmax
  have hh := physical_thermal_fixed_denominator_bound 2 2 (by norm_num) (by norm_num)
    g hg hgmax (shift16 g+167/1000000) 16 (den16:ℝ) (by norm_num) hU
    (by norm_num [a] at hden ⊢; linarith)
  have hs := thermal_exponential_tail16
  norm_num [a,ScalarWarmup.Q0] at hh hs ⊢
  linarith

theorem thermal32 {g : ℝ} (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g) ≤ shift32 g+346/1000000) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian 8 4 g) 16 ≤ (ScalarWarmup.Q1:ℝ) := by
  have hden := denominator32_lower hg hgmax
  have hh := physical_thermal_fixed_denominator_bound 4 2 (by norm_num) (by norm_num)
    g hg hgmax (shift32 g+346/1000000) 16 (den32:ℝ) (by norm_num) hU
    (by norm_num [a] at hden ⊢; linarith)
  have hs := thermal_exponential_tail32
  norm_num [a,ScalarWarmup.Q1] at hh hs ⊢
  linarith

theorem thermal64 {g : ℝ} (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (hU : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 8 g) ≤ shift64 g+800/1000000) :
    relativePartition (PhysicalGram.fullHamiltonian_hermitian 8 8 g) 16 ≤ (ScalarWarmup.Q2:ℝ) := by
  have hden := denominator64_lower hg hgmax
  have hh := physical_thermal_fixed_denominator_bound 4 4 (by norm_num) (by norm_num)
    g hg hgmax (shift64 g+800/1000000) 16 (den64:ℝ) (by norm_num) hU
    (by norm_num [a] at hden ⊢; linarith)
  have hs := thermal_exponential_tail64
  norm_num [a,ScalarWarmup.Q2] at hh hs ⊢
  linarith

end BilayerDressed.CubicSeedThermal

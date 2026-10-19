import Dressed.NumberThermalTail
import Dressed.PhysicalGramLowerBound
import Dressed.ScalarIntervalBounds

/-! Exact cancellation of cubic extensive shifts in the two physical spatial
seed defects. The five energy interval premises are explicit actual-Hamiltonian
bounds, to be supplied by the dressed trial certificates. -/
noncomputable section
namespace BilayerDressed.CubicSeedEnergy
open ScalarInterval ScalarThermal

theorem defect_x {g : ℝ} (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (hlo : shift16 g-167/1000000-(10982/1000000:ℝ)^2/(den16:ℝ) ≤
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g))
    (hhi : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g) ≤
      shift32 g+346/1000000) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g)-
      2*groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) ≤ (ScalarWarmup.dx:ℝ) := by
  have hs := shift_dx hg hgmax
  have he : (ScalarWarmup.dx:ℝ) = (3:ℝ)/8000+346/1000000+
      2*(167/1000000)+2*(10982/1000000)^2/(den16:ℝ) := by
    norm_num [ScalarWarmup.dx, den16]
  rw [he]
  linear_combination hhi + 2*hlo + hs

theorem defect_y {g : ℝ} (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (hlo : shift32 g-346/1000000-(20172/1000000:ℝ)^2/(den32:ℝ) ≤
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g))
    (hhi : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 8 g) ≤
      shift64 g+800/1000000) :
    groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 8 g)-
      2*groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g) ≤ (ScalarWarmup.dy:ℝ) := by
  have hs := shift_dy hg hgmax
  have he : (ScalarWarmup.dy:ℝ) = (3:ℝ)/4000+800/1000000+
      2*(346/1000000)+2*(20172/1000000)^2/(den32:ℝ) := by
    norm_num [ScalarWarmup.dy, den32]
  rw [he]
  linear_combination hhi + 2*hlo + hs

end BilayerDressed.CubicSeedEnergy

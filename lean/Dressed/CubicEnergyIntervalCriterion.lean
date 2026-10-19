import Dressed.CubicSeedThermal
import Dressed.CubicSeedEnergyDefects
import Dressed.PhysicalSeedRatios
import Dressed.PhysicalStandardCriterion

/-! The last finite-to-uniform interface. It consumes actual energy intervals,
not a claimed certificate of their derivation. Only the two smaller boxes need
Temple lower bounds; the 64-rung box needs a variational upper bound. -/
noncomputable section
namespace BilayerDressed.CubicEnergyInterval
open BilayerGap ScalarInterval ScalarThermal

/-- Five actual physical energy bounds suffice for all three genuine seeds. -/
theorem coordinate_bounds {g : ℝ} (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (hu16 : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) ≤ shift16 g+167/1000000)
    (hu32 : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g) ≤ shift32 g+346/1000000)
    (hu64 : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 8 g) ≤ shift64 g+800/1000000)
    (hl16 : shift16 g-167/1000000-(10982/1000000:ℝ)^2/(den16:ℝ) ≤
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g))
    (hl32 : shift32 g-346/1000000-(20172/1000000:ℝ)^2/(den32:ℝ) ≤
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g)) :
    CoordinateWarmup.Bounds (BilayerModel.family g).spectral.partition ⟨4,4,16⟩
      ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0 :=
  PhysicalSeeds.coordinate_bounds_of_energy_thermal g
    (CubicSeedEnergy.defect_x hg hgmax hl16 hu32)
    (CubicSeedEnergy.defect_y hg hgmax hl32 hu64)
    (CubicSeedThermal.thermal16 hg hgmax hu16)
    (CubicSeedThermal.thermal32 hg hgmax hu32)
    (CubicSeedThermal.thermal64 hg hgmax hu64)

/-- The physical all-size gap follows from those five energy intervals. No
moment representation, transfer limit, gap or simple ground state is assumed. -/
theorem uniform_gap {g : ℝ} (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (hu16 : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g) ≤ shift16 g+167/1000000)
    (hu32 : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g) ≤ shift32 g+346/1000000)
    (hu64 : groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 8 g) ≤ shift64 g+800/1000000)
    (hl16 : shift16 g-167/1000000-(10982/1000000:ℝ)^2/(den16:ℝ) ≤
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian 4 4 g))
    (hl32 : shift32 g-346/1000000-(20172/1000000:ℝ)^2/(den32:ℝ) ≤
      groundEnergy (PhysicalGram.fullHamiltonian_hermitian 8 4 g))
    (L : ℕ) (hL : ValidSize L) (hlarge : 256 ≤ L)
    (i k : Fin ((BilayerModel.family g).dim L L : ℕ)) (hik : i ≠ k)
    (hground : ∀ j,((BilayerModel.family g).hermitian L L).eigenvalues i ≤
      ((BilayerModel.family g).hermitian L L).eigenvalues j) :
    PhysicalWarmup.gapLowerBound < ((BilayerModel.family g).hermitian L L).eigenvalues k-
      ((BilayerModel.family g).hermitian L L).eigenvalues i :=
  PhysicalWarmup.uniform_gap_of_seed hg (coordinate_bounds hg hgmax hu16 hu32 hu64 hl16 hl32)
    L hL hlarge i k hik hground

end BilayerDressed.CubicEnergyInterval

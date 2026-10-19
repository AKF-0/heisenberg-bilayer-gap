import Dressed.CubicEnergyIntervalCriterion
import Dressed.CubicTrialEnergy
import Dressed.CubicSeedSupersolution

/-! The final concrete cubic-trial interface. This file does not claim that its
five residual inequalities are proved: it records exactly the still-required
actual Hilbert-space inputs, and turns them into the three physical seeds.
No finite spectral, partition, transfer, or simple-ground-state premise remains.
-/
noncomputable section
open scoped RealInnerProductSpace
namespace BilayerDressed.CubicTrialSeed
open BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open ScalarInterval ScalarThermal

abbrev kernel16 (g : ℝ) := cubicKernel (graph 2 2 four_by_four_conditions) g
abbrev kernel32 (g : ℝ) := cubicKernel (graph 4 2 eight_by_four_conditions) g
abbrev kernel64 (g : ℝ) := cubicKernel (graph 4 4 eight_by_eight_conditions) g

/-- These are bounds on the actual physical trial vector, not arbitrary scalar
certificate fields. The 64-rung box needs a mean bound only. -/
structure Bounds (g : ℝ) : Prop where
  mean16 : |⟪dressedVector (kernel16 g),
    (CartesianBasis.fullHamiltonian 2 2 g).toEuclideanLin (dressedVector (kernel16 g))-
      shift16 g • dressedVector (kernel16 g)⟫| ≤ 167/1000000
  mean32 : |⟪dressedVector (kernel32 g),
    (CartesianBasis.fullHamiltonian 4 2 g).toEuclideanLin (dressedVector (kernel32 g))-
      shift32 g • dressedVector (kernel32 g)⟫| ≤ 346/1000000
  mean64 : |⟪dressedVector (kernel64 g),
    (CartesianBasis.fullHamiltonian 4 4 g).toEuclideanLin (dressedVector (kernel64 g))-
      shift64 g • dressedVector (kernel64 g)⟫| ≤ 800/1000000
  norm16 : ‖(CartesianBasis.fullHamiltonian 2 2 g).toEuclideanLin (dressedVector (kernel16 g))-
      shift16 g • dressedVector (kernel16 g)‖ ≤ 10982/1000000
  norm32 : ‖(CartesianBasis.fullHamiltonian 4 2 g).toEuclideanLin (dressedVector (kernel32 g))-
      shift32 g • dressedVector (kernel32 g)‖ ≤ 20172/1000000

/-- The true cubic trial inequalities imply all finite inputs to the checked
six-step physical bootstrap. This theorem is conditional on those inequalities. -/
theorem coordinate_bounds {g : ℝ} (hg : 0 ≤ g) (hgmax : g ≤ 1/10)
    (h : Bounds g) :
    CoordinateWarmup.Bounds (BilayerModel.family g).spectral.partition ⟨4,4,16⟩
      ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0 := by
  have hu16 := CubicTrialEnergy.physical_upper 2 2 (by omega) (by omega) g
    (kernel16 g) (shift16 g) (167/1000000) h.mean16
  have hu32 := CubicTrialEnergy.physical_upper 4 2 (by omega) (by omega) g
    (kernel32 g) (shift32 g) (346/1000000) h.mean32
  have hu64 := CubicTrialEnergy.physical_upper 4 4 (by omega) (by omega) g
    (kernel64 g) (shift64 g) (800/1000000) h.mean64
  have hl16 := CubicTrialEnergy.physical_lower 2 2 (by omega) (by omega) g hg hgmax
    (kernel16 g) (shift16 g) (167/1000000) (10982/1000000) (den16:ℝ)
    h.mean16 h.norm16 (by norm_num [den16])
    (by have hd := denominator16_lower hg hgmax
        norm_num [a] at hd ⊢
        linarith)
  have hl32 := CubicTrialEnergy.physical_lower 4 2 (by omega) (by omega) g hg hgmax
    (kernel32 g) (shift32 g) (346/1000000) (20172/1000000) (den32:ℝ)
    h.mean32 h.norm32 (by norm_num [den32])
    (by have hd := denominator32_lower hg hgmax
        norm_num [a] at hd ⊢
        linarith)
  exact CubicEnergyInterval.coordinate_bounds hg hgmax hu16 hu32 hu64 hl16 hl32

/-- A conditional all-size theorem with only five explicit actual cubic-trial
inequalities. Constructing `Bounds g` is the remaining coefficient obligation. -/
theorem uniform_gap {g : ℝ} (hg : 0 ≤ g) (hgmax : g ≤ 1/10) (h : Bounds g)
    (L : ℕ) (hL : ValidSize L) (hlarge : 256 ≤ L)
    (i k : Fin ((BilayerModel.family g).dim L L : ℕ)) (hik : i ≠ k)
    (hground : ∀ j,((BilayerModel.family g).hermitian L L).eigenvalues i ≤
      ((BilayerModel.family g).hermitian L L).eigenvalues j) :
    PhysicalWarmup.gapLowerBound < ((BilayerModel.family g).hermitian L L).eigenvalues k-
      ((BilayerModel.family g).hermitian L L).eigenvalues i :=
  PhysicalWarmup.uniform_gap_of_seed hg (coordinate_bounds hg hgmax h) L hL hlarge i k hik hground

end BilayerDressed.CubicTrialSeed

import Dressed.CoordinateWarmup
import Gap.UniformBilayerGap

/-! The six-warmup criterion for the actual bilayer Hamiltonian family. Both
spatial transfer limits are constructed by the pinned first-project theorem.
Only the three explicitly displayed finite seed bounds remain to be assembled. -/
noncomputable section
namespace BilayerDressed.PhysicalWarmup
open BilayerGap

/-- The intended positive uniform gap constant after six finite warmups. -/
def gapLowerBound : ℝ := Real.log (200/13)/1024

theorem gapLowerBound_pos : 0 < gapLowerBound :=
  div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- Conditional only on the three concrete finite-volume seeds, not on any
transfer, moment representation, spectral comparison or ground simplicity. -/
theorem uniform_gap_of_seed {g : ℝ} (hg : 0 ≤ g)
    (hseed : CoordinateWarmup.Bounds (BilayerModel.family g).spectral.partition
      ⟨4,4,16⟩ ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0)
    (L : ℕ) (hL : ValidSize L) (hlarge : 256 ≤ L)
    (i k : Fin ((BilayerModel.family g).dim L L : ℕ)) (hik : i ≠ k)
    (hground : ∀ j,((BilayerModel.family g).hermitian L L).eigenvalues i ≤
      ((BilayerModel.family g).hermitian L L).eigenvalues j) :
    gapLowerBound < ((BilayerModel.family g).hermitian L L).eigenvalues k-
      ((BilayerModel.family g).hermitian L L).eigenvalues i := by
  exact CoordinateWarmup.square_gap_of_initial_bounds (BilayerModel.family g).spectral
    (fun _ hb => (BilayerModel.transfers hg hb).toMomentLimits)
    hseed L hL hlarge i k hik hground

theorem unique_ground_of_seed {g : ℝ} (hg : 0 ≤ g)
    (hseed : CoordinateWarmup.Bounds (BilayerModel.family g).spectral.partition
      ⟨4,4,16⟩ ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0)
    (L : ℕ) (hL : ValidSize L) (hlarge : 256 ≤ L) :
    ∃! i : Fin ((BilayerModel.family g).dim L L : ℕ), ∀ j,
      ((BilayerModel.family g).hermitian L L).eigenvalues i ≤
        ((BilayerModel.family g).hermitian L L).eigenvalues j := by
  exact CoordinateWarmup.unique_ground_of_initial_bounds (BilayerModel.family g).spectral
    (fun _ hb => (BilayerModel.transfers hg hb).toMomentLimits) hseed L hL hlarge

end BilayerDressed.PhysicalWarmup

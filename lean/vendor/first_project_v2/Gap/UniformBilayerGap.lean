import Gap.BilayerModel
import Gap.HistoryStripTorus

/-!
# Uniform spectral gap of the concrete bilayer Hamiltonian

Every model input is now constructed: the real rung matrices, the torus
nearest-neighbor Hamiltonian, both spatial transfer limits, and the three
finite seed inequalities. The theorem below has no spectral-representation,
transfer-convergence, purity, or seed assumption.
-/
noncomputable section
namespace BilayerGap.BilayerModel
open RealRungOperators

/-- Both spatial transfer limits for the actual Hamiltonian, not an assumed bridge. -/
def transfers {g b : ℝ} (hg : 0 ≤ g) (hb : 0 < b) :
    FiniteSymmetricSpatialLimits (fun L M => (family g).spectral.partition ⟨L,M,b⟩) := by
  have he : (fun L M => (family g).spectral.partition ⟨L,M,b⟩) =
      (fun L M => TraceConvexity.partition (Torus.fullHamiltonian L M h G g) b) := by
    funext L M
    exact family_partition g ⟨L,M,b⟩
  rw [he]
  exact History.fullHamiltonianSpatialLimits h G g b hg hb.le

/-- A strictly positive constant independent of system size. -/
def gapLowerBound : ℝ := Real.log (100/27)/14

theorem gapLowerBound_pos : 0 < gapLowerBound :=
  div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- Uniform gap between actual eigenvalues of the concrete finite bilayer matrix. -/
theorem uniform_gap {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1/1000)
    (L : ℕ) (hL : ValidSize L)
    (i k : Fin ((family g).dim L L : ℕ)) (hik : i ≠ k)
    (hmin : ∀ j, ((family g).hermitian L L).eigenvalues i ≤
      ((family g).hermitian L L).eigenvalues j) :
    gapLowerBound < ((family g).hermitian L L).eigenvalues k -
      ((family g).hermitian L L).eigenvalues i := by
  exact (family g).spectral.transfer_square_gap_one_percent
    (fun _ hb => transfers hg0 hb) 4 14 ⟨by norm_num, by decide⟩ (by norm_num)
    (narrow_seed hg0 hg) L hL hL.1 i k hik hmin

/-- The lowest eigenvalue is simple; no ground nondegeneracy is assumed. -/
theorem unique_ground {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1/1000)
    (L : ℕ) (hL : ValidSize L) :
    ∃! i : Fin ((family g).dim L L : ℕ), ∀ j,
      ((family g).hermitian L L).eigenvalues i ≤
        ((family g).hermitian L L).eigenvalues j := by
  exact (family g).spectral.transfer_unique_ground_of_one_percent
    (fun _ hb => transfers hg0 hb) 4 14 ⟨by norm_num, by decide⟩ (by norm_num)
    (narrow_seed hg0 hg) L hL hL.1

/-- An unconditional ground index and the same positive gap at every valid size. -/
theorem uniform_ground_gap {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1/1000)
    (L : ℕ) (hL : ValidSize L) :
    ∃ i : Fin ((family g).dim L L : ℕ),
      (∀ j, ((family g).hermitian L L).eigenvalues i ≤
        ((family g).hermitian L L).eigenvalues j) ∧
      ∀ k, k ≠ i → gapLowerBound < ((family g).hermitian L L).eigenvalues k -
        ((family g).hermitian L L).eigenvalues i := by
  obtain ⟨i, hi, _⟩ := unique_ground hg0 hg L hL
  exact ⟨i, hi, fun k hki => uniform_gap hg0 hg L hL i k hki.symm hi⟩

#print axioms transfers
#print axioms uniform_gap
#print axioms unique_ground
#print axioms uniform_ground_gap
end BilayerGap.BilayerModel

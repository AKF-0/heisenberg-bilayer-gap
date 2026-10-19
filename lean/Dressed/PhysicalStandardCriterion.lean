import Dressed.PhysicalWarmupCriterion
import Gap.PhysicalGapTheorem

/-! The six-warmup conclusion on the explicit complex Pauli spin Hamiltonian.
The complete eigenbasis is imported from the pinned checked physical basis
bridge. The only conditional inputs are the three displayed actual finite seeds. -/
noncomputable section
namespace BilayerDressed.PhysicalStandard
open BilayerGap

/-- All levels of the actual standard spin-half bilayer, including multiplicity,
with a unique lowest level and the six-warmup uniform positive separation. -/
theorem standard_spin_gap_of_seed {g : ℝ} (hg : 0 ≤ g)
    (hseed : CoordinateWarmup.Bounds (BilayerModel.family g).spectral.partition
      ⟨4,4,16⟩ ScalarWarmup.a0 ScalarWarmup.b0 ScalarWarmup.c0)
    (L : ℕ) (hL : ValidSize L) (hlarge : 256 ≤ L) :
    ∃ P Q : Matrix (Fin ((BilayerModel.family g).dim L L : ℕ))
        (Fin ((BilayerModel.family g).dim L L : ℕ)) ℂ,
    ∃ i₀ : Fin ((BilayerModel.family g).dim L L : ℕ),
      P*Q=1 ∧ Q*P=1 ∧ PhysicalGap.physicalMatrix L L g*P=
        P*Matrix.diagonal (fun i => (((BilayerModel.family g).hermitian L L).eigenvalues i : ℂ)) ∧
      (∀ i, ((BilayerModel.family g).hermitian L L).eigenvalues i₀ ≤
        ((BilayerModel.family g).hermitian L L).eigenvalues i) ∧
      (∀ i, ((∀ j, ((BilayerModel.family g).hermitian L L).eigenvalues i ≤
        ((BilayerModel.family g).hermitian L L).eigenvalues j)) → i=i₀) ∧
      ∀ i, i≠i₀ → PhysicalWarmup.gapLowerBound <
        ((BilayerModel.family g).hermitian L L).eigenvalues i-
          ((BilayerModel.family g).hermitian L L).eigenvalues i₀ := by
  obtain ⟨P,Q,hPQ,hQP,hdiag⟩ := PhysicalGap.physical_complete_eigenbasis L L g
  obtain ⟨i₀,hmin,hunique⟩ := PhysicalWarmup.unique_ground_of_seed hg hseed L hL hlarge
  refine ⟨P,Q,i₀,hPQ,hQP,hdiag,hmin,hunique,?_⟩
  intro i hi
  exact PhysicalWarmup.uniform_gap_of_seed hg hseed L hL hlarge i₀ i hi.symm hmin

end BilayerDressed.PhysicalStandard

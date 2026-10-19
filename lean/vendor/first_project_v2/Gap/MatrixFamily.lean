import Gap.LimitCriterion
import Gap.TraceConvexity

/-! A finite Gibbs family obtained from the genuine eigenvalues of a concrete
Hermitian matrix family. This interface does not accept an arbitrary assigned
energy list, and the partition equality is derived from the spectral theorem. -/
noncomputable section
namespace BilayerGap

structure HamiltonianFamily where
  dim : ℕ → ℕ → ℕ+
  matrix : ∀ L M, Matrix (Fin (dim L M : ℕ)) (Fin (dim L M : ℕ)) ℝ
  hermitian : ∀ L M, (matrix L M).IsHermitian

def HamiltonianFamily.spectral (H : HamiltonianFamily) : SpectralFamily where
  dim := H.dim
  energy := fun L M => (H.hermitian L M).eigenvalues

theorem HamiltonianFamily.partition_eq (H : HamiltonianFamily) (v : Volume) :
    H.spectral.partition v = TraceConvexity.partition (H.matrix v.x v.y) v.beta := by
  rw [TraceConvexity.partition_eq_sum (H.hermitian v.x v.y)]
  rfl

/-- The full criterion now concludes a gap between actual matrix eigenvalues.
Model-specific seed and transfer constructions remain explicit inputs here. -/
theorem HamiltonianFamily.gap_of_transfer_seed (H : HamiltonianFamily)
    (transfers : ∀ b : ℝ, 0 < b → FiniteSymmetricSpatialLimits
      (fun L M => TraceConvexity.partition (H.matrix L M) b))
    (n : ℕ) (b : ℝ) (hn : ValidSize n) (hb : 0 < b)
    (seed : 1-staircaseA H.spectral.partition ⟨n,n,b⟩ ≤ 1/100 ∧
      1-staircaseB H.spectral.partition ⟨n,n,b⟩ ≤ 1/100 ∧
      1-staircaseC H.spectral.partition ⟨n,n,b⟩ ≤ 1/100)
    (L : ℕ) (hL : ValidSize L) (hnL : n ≤ L)
    (i k : Fin (H.dim L L : ℕ)) (hik : i ≠ k)
    (hmin : ∀ j, (H.hermitian L L).eigenvalues i ≤ (H.hermitian L L).eigenvalues j) :
    Real.log (100/27)/b < (H.hermitian L L).eigenvalues k -
      (H.hermitian L L).eigenvalues i := by
  apply H.spectral.transfer_square_gap_one_percent ?_ n b hn hb seed L hL hnL i k hik hmin
  intro β hβ
  simpa only [H.partition_eq] using transfers β hβ

#print axioms HamiltonianFamily.partition_eq
#print axioms HamiltonianFamily.gap_of_transfer_seed
end BilayerGap

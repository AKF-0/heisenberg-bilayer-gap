import Gap.TorusHamiltonian
import Gap.RealRungOperators
import Gap.RungMatchingSeed
import Gap.MatrixFamily
import Gap.PartitionSeed

/-! The explicit bilayer model in its certified real rung coordinates.
No partition bound is part of the model definition. The finite seed bounds
are derived from the actual four torus matchings and local spin matrices. -/
noncomputable section
namespace BilayerGap.BilayerModel
open Matrix RealRungOperators
open scoped Matrix.Norms.Operator

/-- Shifted spin-half bilayer Heisenberg Hamiltonian, with unit rung coupling. -/
def hamiltonian (L M : ℕ) (g : ℝ) :
    Matrix (Torus.FullConfig L M) (Torus.FullConfig L M) ℝ :=
  Torus.fullHamiltonian L M h G g

def partition (L M : ℕ) (g b : ℝ) : ℝ :=
  TraceConvexity.partition (hamiltonian L M g) b

theorem localPair_eq (t : ℝ) : Torus.localPair h G t = RealRungPair.hamiltonian t :=
  (pair_hamiltonian_eq t).symm

/-- The actual nearest-neighbor matrix is the four-matching average. -/
theorem even_eq_four_matching (n m : ℕ) (g : ℝ) :
    hamiltonian (2*n) (2*m) g =
      RungMatchingSeed.fourMatchingHamiltonian (Torus.PairCount n m) (4*g)
        (Torus.matchingBasis n m) := by
  unfold hamiltonian
  rw [Torus.fullHamiltonian_even_eq_matching_average]
  simp only [RungMatchingSeed.fourMatchingHamiltonian,
    RungMatchingSeed.pairedHamiltonian, Torus.matchingBlock, localPair_eq]

theorem even_hermitian (n m : ℕ) (g : ℝ) :
    (hamiltonian (2*n) (2*m) g).IsHermitian := by
  rw [even_eq_four_matching]
  exact RungMatchingSeed.four_matching_hermitian _ _ _

/-- The true product-singlet diagonal has zero energy in every even volume. -/
theorem even_vacuum (n m : ℕ) (g : ℝ) :
    hamiltonian (2*n) (2*m) g (fun _ => 0) (fun _ => 0) = 0 :=
  Torus.hamiltonian_vacuum_diagonal n m h G g h_vacuum
    (fun a => G_diagonal_zero a 0)

/-- Genuine partition lower bound from the shared product-singlet state. -/
theorem even_partition_lower (n m : ℕ) (g b : ℝ) (hb : 0 ≤ b) :
    1 ≤ partition (2*n) (2*m) g b :=
  TraceConvexity.one_le_partition_of_zero_diagonal (even_hermitian n m g)
    (fun _ => 0) (even_vacuum n m g) hb

/-- Genuine finite-volume seed upper bound, derived from the physical matrix. -/
theorem even_partition_narrow (n m : ℕ) {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1/1000) :
    partition (2*n) (2*m) g 14 ≤ (10001/10000 : ℝ)^(2*n*m) := by
  unfold partition
  rw [even_eq_four_matching]
  exact RungMatchingSeed.four_matching_narrow_bound _ hg0 hg _

theorem even_partition_wide (n m : ℕ) {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1/400) :
    partition (2*n) (2*m) g 14 ≤ (1+(SeedCertificate.wideEta:ℝ))^(2*n*m) := by
  unfold partition
  rw [even_eq_four_matching]
  exact RungMatchingSeed.four_matching_wide_bound _ hg0 hg _

/-- Hermiticity holds for the actual model at all sizes, not only the valid even ones. -/
theorem hermitian (L M : ℕ) (g : ℝ) : (hamiltonian L M g).IsHermitian := by
  apply Torus.fullHamiltonian_hermitian L M h G g
  · change h.conjTranspose = h
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact h_symmetric
  · exact G_antisymmetric

/-- The finite spectral family is built from this actual matrix, not assigned energies. -/
def family (g : ℝ) : HamiltonianFamily where
  dim := fun L M => ⟨Fintype.card (Torus.FullConfig L M), Fintype.card_pos⟩
  matrix := fun L M => Matrix.reindex (Fintype.equivFin (Torus.FullConfig L M))
    (Fintype.equivFin (Torus.FullConfig L M)) (hamiltonian L M g)
  hermitian := fun L M => (hermitian L M g).submatrix _

theorem family_partition (g : ℝ) (v : Volume) :
    (family g).spectral.partition v = partition v.x v.y g v.beta := by
  rw [HamiltonianFamily.partition_eq]
  unfold TraceConvexity.partition TraceConvexity.traceExp partition
  change Matrix.trace (NormedSpace.exp ℝ
    (Matrix.reindex (Fintype.equivFin (Torus.FullConfig v.x v.y))
      (Fintype.equivFin (Torus.FullConfig v.x v.y)) ((-v.beta) • hamiltonian v.x v.y g))) = _
  rw [TwoRungTrace.trace_exp_reindex]
  rfl

/-- The three finite seed defects are derived for the concrete Hamiltonian. -/
theorem narrow_seed {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 1/1000) :
    1-staircaseA (family g).spectral.partition ⟨4,4,14⟩ ≤ 1/100 ∧
    1-staircaseB (family g).spectral.partition ⟨4,4,14⟩ ≤ 1/100 ∧
    1-staircaseC (family g).spectral.partition ⟨4,4,14⟩ ≤ 1/100 := by
  apply PartitionSeed.narrow_staircase
  · exact (family g).spectral.partition_pos
  · rw [family_partition]
    exact even_partition_narrow 2 2 hg0 hg
  · rw [family_partition]
    exact even_partition_narrow 4 2 hg0 hg
  · rw [family_partition]
    exact even_partition_narrow 4 4 hg0 hg
  · rw [family_partition]
    exact even_partition_lower 4 2 g 14 (by norm_num)
  · rw [family_partition]
    exact even_partition_lower 4 4 g 14 (by norm_num)
  · rw [family_partition]
    exact even_partition_lower 4 4 g 28 (by norm_num)

#print axioms even_eq_four_matching
#print axioms even_partition_lower
#print axioms even_partition_narrow
#print axioms family_partition
#print axioms narrow_seed
end BilayerGap.BilayerModel

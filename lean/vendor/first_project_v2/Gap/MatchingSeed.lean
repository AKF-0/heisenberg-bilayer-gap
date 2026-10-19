import Gap.TwoRungTrace
import Gap.ClusterProducts
import Gap.TraceConvexity

/-!
# The finite matching seed from actual matrices

A matching is represented by an explicit basis equivalence to independent
clusters. This file proves the matrix trace upper bound from those equivalences;
it does not assume that bound. Constructing the four concrete periodic-lattice
pairing equivalences remains a separate model obligation.
-/
noncomputable section
namespace BilayerGap
namespace MatchingSeed
open Matrix TwoRung ClusterProducts
open scoped Kronecker Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem realHamiltonian_hermitian (t : ℝ) : (realHamiltonian t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hr := congrArg (fun A : QMat => (A i j : ℝ)) rung_symmetric
  have hi := congrArg (fun A : QMat => (A i j : ℝ)) interaction_symmetric
  simp only [Matrix.transpose_apply] at hr hi
  simp [realHamiltonian, toReal, hr, hi]

theorem tensorSum_hermitian {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (tensorSum A B).IsHermitian := by
  change (A ⊗ₖ (1 : Matrix n n ℝ) + (1 : Matrix m m ℝ) ⊗ₖ B)ᴴ = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_kronecker, hA.eq, hB.eq, Matrix.conjTranspose_one]
  simp only [Matrix.conjTranspose_one, tensorSum]

theorem independent_hermitian (A : Matrix (Fin 16) (Fin 16) ℝ)
    (hA : A.IsHermitian) (k : ℕ) : (independentHamiltonian A k).IsHermitian := by
  induction k with
  | zero => simp [independentHamiltonian]
  | succ k ih => exact tensorSum_hermitian A (independentHamiltonian A k) hA ih

/-- An actual paired Hamiltonian, not just an assigned partition value. -/
def pairedHamiltonian (k : ℕ) (t : ℝ) (e : PowerIndex k ≃ ι) : Matrix ι ι ℝ :=
  Matrix.reindex e e (independentHamiltonian (realHamiltonian t) k)

omit [Fintype ι] [DecidableEq ι] in
theorem paired_hermitian (k : ℕ) (t : ℝ) (e : PowerIndex k ≃ ι) :
    (pairedHamiltonian k t e).IsHermitian :=
  (independent_hermitian _ (realHamiltonian_hermitian t) k).submatrix e.symm

/-- The matching's thermal trace is derived from tensor factorization and the
verified local matrix trace formula. -/
theorem paired_partition (k : ℕ) (t b : ℝ) (e : PowerIndex k ≃ ι) :
    TraceConvexity.partition (pairedHamiltonian k t e) b =
      ClusterSeed.partition t b ^ k := by
  unfold TraceConvexity.partition TraceConvexity.traceExp pairedHamiltonian
  have hs : (-b) • Matrix.reindex e e (independentHamiltonian (realHamiltonian t) k) =
      Matrix.reindex e e ((-b) • independentHamiltonian (realHamiltonian t) k) := rfl
  rw [hs, TwoRungTrace.trace_exp_reindex, thermal_trace_independent,
    TwoRungTrace.trace_exp_eq_partition]

/-- Four equivalent perfect-matching Hamiltonians with their genuine matrix average. -/
def fourMatchingHamiltonian (k : ℕ) (t : ℝ) (e : Fin 4 → PowerIndex k ≃ ι) :
    Matrix ι ι ℝ := (1/4 : ℝ) • ∑ c, pairedHamiltonian k t (e c)

/-- The cluster upper bound needs ordinary trace-exp convexity, not the stronger
log-trace convexity: all four matching partition functions are exactly equal. -/
theorem four_matching_partition_bound (k : ℕ) (t b : ℝ)
    (e : Fin 4 → PowerIndex k ≃ ι) :
    TraceConvexity.partition (fourMatchingHamiltonian k t e) b ≤
      ClusterSeed.partition t b ^ k := by
  apply TraceConvexity.partition_average_four_le
    (fun c => pairedHamiltonian k t (e c))
    (fun c => paired_hermitian k t (e c)) b (ClusterSeed.partition t b ^ k)
  intro c
  exact (paired_partition k t b (e c)).le

omit [Fintype ι] [DecidableEq ι] in
theorem four_matching_hermitian (k : ℕ) (t : ℝ)
    (e : Fin 4 → PowerIndex k ≃ ι) : (fourMatchingHamiltonian k t e).IsHermitian := by
  have h := TraceConvexity.hermitian_weighted_sum (fun _ : Fin 4 => (1/4 : ℝ))
    (fun c => pairedHamiltonian k t (e c)) (fun c => paired_hermitian k t (e c))
  simpa only [fourMatchingHamiltonian, Finset.smul_sum] using h

/-- A genuine matrix partition bound at the narrow analytic endpoint. -/
theorem four_matching_narrow_bound (k : ℕ) {g : ℝ} (hg0 : 0≤g) (hg : g≤1/1000)
    (e : Fin 4 → PowerIndex k ≃ ι) :
    TraceConvexity.partition (fourMatchingHamiltonian k (4*g) e) 14 ≤
      (10001/10000 : ℝ)^k := by
  apply (four_matching_partition_bound k (4*g) 14 e).trans
  have hp : 0 ≤ ClusterSeed.partition (4*g) 14 := by
    unfold ClusterSeed.partition
    positivity
  exact pow_le_pow_left₀ hp
    (ClusterSeed.narrow_partition_bound (by linarith) (by linarith)).le k

/-- The wider exact-eta bound also controls the genuine matching-average matrix. -/
theorem four_matching_wide_bound (k : ℕ) {g : ℝ} (hg0 : 0≤g) (hg : g≤1/400)
    (e : Fin 4 → PowerIndex k ≃ ι) :
    TraceConvexity.partition (fourMatchingHamiltonian k (4*g) e) 14 ≤
      (1+(SeedCertificate.wideEta : ℝ))^k := by
  apply (four_matching_partition_bound k (4*g) 14 e).trans
  have hp : 0 ≤ ClusterSeed.partition (4*g) 14 := by
    unfold ClusterSeed.partition
    positivity
  exact pow_le_pow_left₀ hp
    (ClusterSeed.wide_partition_bound (by linarith) (by linarith)) k

/-- The lower bound is separate: a common physical test state must be supplied.
Arbitrary basis permutations are not assumed to preserve a singlet product. -/
theorem four_matching_lower_bound (k : ℕ) (t : ℝ)
    (e : Fin 4 → PowerIndex k ≃ ι) (v : ι→ℝ) (hv : v≠0)
    (hE : dotProduct v (fourMatchingHamiltonian k t e *ᵥ v) ≤ 0)
    {b : ℝ} (hb : 0≤b) : 1≤TraceConvexity.partition (fourMatchingHamiltonian k t e) b :=
  TraceConvexity.one_le_partition_of_nonpos_expectation
    (four_matching_hermitian k t e) v hv hE hb

#print axioms realHamiltonian_hermitian
#print axioms paired_partition
#print axioms four_matching_partition_bound
#print axioms four_matching_narrow_bound
#print axioms four_matching_wide_bound
#print axioms four_matching_lower_bound
end MatchingSeed
end BilayerGap

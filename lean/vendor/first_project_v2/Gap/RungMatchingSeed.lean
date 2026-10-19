import Gap.RealRungPair
import Gap.MatchingSeed

/-! Matching seed bounds in the actual real rung coordinates. The local pair
partition is not postulated: it is linked by a checked rational similarity to
the 16-level two-rung matrix. The concrete torus pairings are supplied separately. -/
noncomputable section
namespace BilayerGap.RungMatchingSeed
open Matrix ClusterProducts
open scoped Matrix.Norms.Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open MatchingSeed (independent_hermitian)

/-- An actual paired Hamiltonian, not just an assigned partition value. -/
def pairedHamiltonian (k : ℕ) (t : ℝ) (e : PowerIndex k ≃ ι) : Matrix ι ι ℝ :=
  Matrix.reindex e e (independentHamiltonian (RealRungPair.hamiltonian t) k)

omit [Fintype ι] [DecidableEq ι] in
theorem paired_hermitian (k : ℕ) (t : ℝ) (e : PowerIndex k ≃ ι) :
    (pairedHamiltonian k t e).IsHermitian :=
  (independent_hermitian _ (RealRungPair.hamiltonian_hermitian t) k).submatrix e.symm

/-- The matching's thermal trace is derived from tensor factorization and the
verified local matrix trace formula. -/
theorem paired_partition (k : ℕ) (t b : ℝ) (e : PowerIndex k ≃ ι) :
    TraceConvexity.partition (pairedHamiltonian k t e) b =
      ClusterSeed.partition t b ^ k := by
  unfold TraceConvexity.partition TraceConvexity.traceExp pairedHamiltonian
  have hs : (-b) • Matrix.reindex e e (independentHamiltonian (RealRungPair.hamiltonian t) k) =
      Matrix.reindex e e ((-b) • independentHamiltonian (RealRungPair.hamiltonian t) k) := rfl
  rw [hs, TwoRungTrace.trace_exp_reindex, thermal_trace_independent,
    RealRungPair.trace_exp_eq_partition]

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


/-- The product rung-singlet state in the nested independent-cluster basis. -/
def vacuum : (k : ℕ) → PowerIndex k
  | 0 => (0 : Fin 1)
  | k+1 => (0, vacuum k)

theorem independent_vacuum (t : ℝ) (k : ℕ) :
    independentHamiltonian (RealRungPair.hamiltonian t) k (vacuum k) (vacuum k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [independentHamiltonian, vacuum, tensorSum, Matrix.kronecker_apply,
      RealRungPair.hamiltonian_vacuum, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem paired_vacuum (k : ℕ) (t : ℝ) (e : PowerIndex k ≃ ι) :
    pairedHamiltonian k t e (e (vacuum k)) (e (vacuum k)) = 0 := by
  simp [pairedHamiltonian, Matrix.reindex_apply, Matrix.submatrix_apply, independent_vacuum]

/-- The lower bound follows once all four actual basis rearrangements preserve
one explicitly identified product-singlet state. -/
theorem four_matching_lower_bound_of_vacuum (k : ℕ) (t : ℝ)
    (e : Fin 4 → PowerIndex k ≃ ι) (v : ι) (hv : ∀ c, e c (vacuum k) = v)
    {b : ℝ} (hb : 0≤b) :
    1 ≤ TraceConvexity.partition (fourMatchingHamiltonian k t e) b := by
  apply TraceConvexity.one_le_partition_of_zero_diagonal
    (four_matching_hermitian k t e) v ?_ hb
  have hc (c : Fin 4) : pairedHamiltonian k t (e c) v v = 0 := by
    rw [← hv c]
    exact paired_vacuum k t (e c)
  simp [fourMatchingHamiltonian, Matrix.smul_apply, Matrix.sum_apply, hc]

#print axioms four_matching_narrow_bound
#print axioms four_matching_lower_bound_of_vacuum
end BilayerGap.RungMatchingSeed

import Mathlib

/-!
# Finite real-symmetric trace-exponential convexity

The proof uses only finite spectral decomposition and scalar Jensen:
* squared entries of an orthogonal eigenvector matrix are probability weights;
* Peierls' diagonal inequality follows by applying scalar exponential Jensen;
* diagonalize a weighted average, then apply scalar Jensen and Peierls.

The resulting matrix inequality makes no commutativity assumption. In particular,
ordinary trace-exponential convexity suffices for four matching Hamiltonians with
a common partition bound. Full log-trace convexity is unnecessary for that step.

A separate variational theorem proves the lower partition bound from an actual
nonzero test vector with nonpositive expectation. None of the desired partition
bounds appears as an assumed analytic axiom.
-/

open scoped BigOperators
open Matrix
noncomputable section
namespace BilayerGap.TraceConvexity
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of the actual power-series matrix exponential. -/
def traceExp (A : Matrix n n ℝ) : ℝ := Matrix.trace (NormedSpace.exp ℝ A)

lemma exp_unitary_conj (U : Matrix.unitaryGroup n ℝ) (A : Matrix n n ℝ) :
    NormedSpace.exp ℝ ((U : Matrix n n ℝ) * A * star (U : Matrix n n ℝ)) =
      (U : Matrix n n ℝ) * NormedSpace.exp ℝ A * star (U : Matrix n n ℝ) := by
  exact Matrix.exp_units_conj ℝ (unitary.toUnits U) A

lemma diagonal_exp (d : n → ℝ) :
    NormedSpace.exp ℝ (Matrix.diagonal d) = Matrix.diagonal (fun i => Real.exp (d i)) := by
  rw [Matrix.exp_diagonal, Pi.exp_def, ← Real.exp_eq_exp_ℝ]

lemma exp_spectral {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    NormedSpace.exp ℝ A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => Real.exp (hA.eigenvalues i)) *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [exp_unitary_conj]
  simpa only [Function.comp_def] using
    congrArg (fun D => (hA.eigenvectorUnitary : Matrix n n ℝ) * D *
      star (hA.eigenvectorUnitary : Matrix n n ℝ)) (diagonal_exp hA.eigenvalues)

lemma unitary_row_sq_sum (U : Matrix.unitaryGroup n ℝ) (i : n) :
    ∑ j, (U i j) ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix n n ℝ => M i i) (unitary.coe_mul_star_self U)
  simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, pow_two, Matrix.one_apply_eq] using h

lemma diagonal_conj_apply (U : Matrix n n ℝ) (d : n → ℝ) (i : n) :
    (U * Matrix.diagonal d * star U) i i = ∑ j, (U i j)^2 * d j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Peierls' scalar diagonal inequality, proved from the spectral theorem and
finite scalar Jensen. -/
lemma peierls_diagonal {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    Real.exp (A i i) ≤ (NormedSpace.exp ℝ A) i i := by
  have hdiag : A i i = ∑ j, (hA.eigenvectorUnitary i j)^2 * hA.eigenvalues j := by
    conv_lhs => rw [hA.spectral_theorem]
    simpa only [Function.comp_def] using
      diagonal_conj_apply (hA.eigenvectorUnitary : Matrix n n ℝ) hA.eigenvalues i
  rw [hdiag, exp_spectral hA, diagonal_conj_apply]
  exact_mod_cast (convexOn_exp.map_sum_le (t := Finset.univ)
    (w := fun j => (hA.eigenvectorUnitary i j)^2) (p := hA.eigenvalues)
    (fun j _ => sq_nonneg _) (unitary_row_sq_sum hA.eigenvectorUnitary i)
    (fun j _ => Set.mem_univ _))

lemma traceExp_unitary_conj (U : Matrix.unitaryGroup n ℝ) (A : Matrix n n ℝ) :
    traceExp ((U : Matrix n n ℝ) * A * star (U : Matrix n n ℝ)) = traceExp A := by
  unfold traceExp
  rw [exp_unitary_conj, Matrix.trace_mul_cycle, unitary.coe_star_mul_self, one_mul]

lemma traceExp_spectral {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    traceExp A = ∑ i, Real.exp (hA.eigenvalues i) := by
  unfold traceExp
  rw [exp_spectral hA, Matrix.trace_mul_cycle, unitary.coe_star_mul_self, one_mul]
  exact Matrix.trace_diagonal _

omit [Fintype n] [DecidableEq n] in
lemma hermitian_weighted_sum {κ : Type*} [Fintype κ] (w : κ → ℝ)
    (A : κ → Matrix n n ℝ) (hA : ∀ k, (A k).IsHermitian) :
    (∑ k, w k • A k).IsHermitian := by
  change (∑ k, w k • A k)ᴴ = _
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial]
  congr 1
  funext k
  rw [(hA k).eq]

/-- Trace-exponential Jensen inequality for arbitrary finite real symmetric matrices.
No pairwise commutativity is assumed. -/
theorem traceExp_weighted_sum_le {κ : Type*} [Fintype κ] (w : κ → ℝ)
    (A : κ → Matrix n n ℝ) (hA : ∀ k, (A k).IsHermitian)
    (hw : ∀ k, 0 ≤ w k) (hws : ∑ k, w k = 1) :
    traceExp (∑ k, w k • A k) ≤ ∑ k, w k * traceExp (A k) := by
  classical
  let C := ∑ k, w k • A k
  have hC : C.IsHermitian := hermitian_weighted_sum w A hA
  let U := hC.eigenvectorUnitary
  let D := fun k => star (U : Matrix n n ℝ) * A k * (U : Matrix n n ℝ)
  have hD : ∀ k, (D k).IsHermitian := fun k =>
    Matrix.isHermitian_conjTranspose_mul_mul (U : Matrix n n ℝ) (hA k)
  have hdiag (i : n) : hC.eigenvalues i = ∑ k, w k * D k i i := by
    have h := congrArg (fun M : Matrix n n ℝ => M i i) hC.star_mul_self_mul_eq_diagonal
    have heq : star (U : Matrix n n ℝ) * C * (U : Matrix n n ℝ) = ∑ k, w k • D k := by
      simp only [C, D, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    change (star (U : Matrix n n ℝ) * C * (U : Matrix n n ℝ)) i i = _ at h
    rw [heq] at h
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq,
      Function.comp_apply] using h.symm
  have htrace (k : κ) : traceExp (D k) = traceExp (A k) := by
    have h := traceExp_unitary_conj (star U) (A k)
    simpa only [unitary.coe_star, star_star] using h
  calc
    traceExp C = ∑ i, Real.exp (hC.eigenvalues i) := traceExp_spectral hC
    _ ≤ ∑ i, ∑ k, w k * Real.exp (D k i i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [hdiag i]
      exact_mod_cast (convexOn_exp.map_sum_le (t := Finset.univ) (w := w)
        (p := fun k => D k i i) (fun k _ => hw k) hws (fun k _ => Set.mem_univ _))
    _ ≤ ∑ i, ∑ k, w k * (NormedSpace.exp ℝ (D k)) i i := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (peierls_diagonal (hD k) i) (hw k)
    _ = ∑ k, w k * traceExp (D k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.mul_sum]
      rfl
    _ = ∑ k, w k * traceExp (A k) := by simp_rw [htrace]

/-- The actual matrix partition function, with inverse temperature `b`. -/
def partition (H : Matrix n n ℝ) (b : ℝ) : ℝ := traceExp ((-b) • H)

omit [Fintype n] [DecidableEq n] in
lemma hermitian_smul (a : ℝ) {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (a • A).IsHermitian := by
  change (a • A)ᴴ = _
  rw [Matrix.conjTranspose_smul, star_trivial, hA.eq]

/-- The finite spectral formula for the actual matrix partition function. -/
theorem partition_eq_sum {H : Matrix n n ℝ} (hH : H.IsHermitian) (b : ℝ) :
    partition H b = ∑ i, Real.exp (-b * hH.eigenvalues i) := by
  have hspec : H = (hH.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal hH.eigenvalues * star (hH.eigenvectorUnitary : Matrix n n ℝ) :=
    hH.spectral_theorem
  have heq : (-b) • H = (hH.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => -b * hH.eigenvalues i) *
      star (hH.eigenvectorUnitary : Matrix n n ℝ) := by
    conv_lhs => rw [hspec]
    rw [show (fun i => -b * hH.eigenvalues i) = (-b) • hH.eigenvalues from rfl,
      Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  unfold partition
  rw [heq, traceExp_unitary_conj]
  unfold traceExp
  rw [diagonal_exp, Matrix.trace_diagonal]

/-- Variational consequence of positive-definite spectral characterization.
The test vector need only be nonzero; it need not be normalized. -/
theorem exists_nonpos_eigenvalue_of_expectation {H : Matrix n n ℝ}
    (hH : H.IsHermitian) (v : n → ℝ) (hv : v ≠ 0)
    (hE : dotProduct v (H *ᵥ v) ≤ 0) : ∃ i, hH.eigenvalues i ≤ 0 := by
  by_contra! hn
  have hpos : H.PosDef := hH.posDef_iff_eigenvalues_pos.mpr hn
  have hp := hpos.2 v hv
  simp only [star_trivial] at hp
  exact (not_lt_of_ge hE) hp

/-- A nonpositive test-state expectation proves `Z ≥ 1`, without an assumed
lower partition bound and without any entrywise positivity assumption. -/
theorem one_le_partition_of_nonpos_expectation {H : Matrix n n ℝ}
    (hH : H.IsHermitian) (v : n → ℝ) (hv : v ≠ 0)
    (hE : dotProduct v (H *ᵥ v) ≤ 0) {b : ℝ} (hb : 0 ≤ b) :
    1 ≤ partition H b := by
  obtain ⟨i, hi⟩ := exists_nonpos_eigenvalue_of_expectation hH v hv hE
  rw [partition_eq_sum hH b]
  calc
    1 ≤ Real.exp (-b * hH.eigenvalues i) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
        (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hb) hi)
    _ ≤ ∑ j, Real.exp (-b * hH.eigenvalues j) :=
      Finset.single_le_sum (f := fun j => Real.exp (-b * hH.eigenvalues j))
        (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

/-- Partition functions are convex in a finite real symmetric Hamiltonian,
for every real inverse temperature. -/
theorem partition_weighted_sum_le {κ : Type*} [Fintype κ] (w : κ → ℝ)
    (H : κ → Matrix n n ℝ) (hH : ∀ k, (H k).IsHermitian)
    (hw : ∀ k, 0 ≤ w k) (hws : ∑ k, w k = 1) (b : ℝ) :
    partition (∑ k, w k • H k) b ≤ ∑ k, w k * partition (H k) b := by
  have h := traceExp_weighted_sum_le w (fun k => (-b) • H k)
    (fun k => hermitian_smul _ (hH k)) hw hws
  have heq : (-b) • (∑ k, w k • H k) = ∑ k, w k • ((-b) • H k) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun k _ => smul_comm (-b) (w k) (H k))
  simpa only [partition, heq] using h

/-- Four possibly noncommuting Hamiltonians with a common partition bound
have the same bound at their average. This is the matching-seed bridge. -/
theorem partition_average_four_le (H : Fin 4 → Matrix n n ℝ)
    (hH : ∀ k, (H k).IsHermitian) (b z : ℝ)
    (hZ : ∀ k, partition (H k) b ≤ z) :
    partition ((1 / 4 : ℝ) • ∑ k, H k) b ≤ z := by
  have h := partition_weighted_sum_le (fun _ : Fin 4 => (1 / 4 : ℝ)) H hH
    (by intro k; norm_num) (by norm_num) b
  rw [← Finset.smul_sum] at h
  calc
    partition ((1 / 4 : ℝ) • ∑ k, H k) b ≤
        ∑ k, (1 / 4 : ℝ) * partition (H k) b := h
    _ ≤ ∑ _k : Fin 4, (1 / 4 : ℝ) * z := by
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hZ k) (by norm_num))
    _ = z := by simp

/-- A zero diagonal entry is a sufficient special case of the test-vector
criterion; no entrywise sign condition on the Hamiltonian is needed. -/
theorem one_le_partition_of_zero_diagonal {H : Matrix n n ℝ}
    (hH : H.IsHermitian) (i : n) (hii : H i i = 0) {b : ℝ} (hb : 0 ≤ b) :
    1 ≤ partition H b := by
  apply one_le_partition_of_nonpos_expectation hH (Pi.single i 1)
  · intro hz
    have h := congrFun hz i
    simp at h
  · simp only [Matrix.mulVec_single_one, single_dotProduct, one_mul,
      Matrix.col_apply, hii, le_refl]
  · exact hb

#print axioms peierls_diagonal
#print axioms traceExp_weighted_sum_le
#print axioms partition_average_four_le
#print axioms one_le_partition_of_nonpos_expectation
end BilayerGap.TraceConvexity

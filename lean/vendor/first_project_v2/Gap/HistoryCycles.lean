import Mathlib

/-!
# Finite cyclic state sums and matrix powers

These are exact finite algebraic identities. No positivity, symmetry, or spectral
assumption is needed. The cyclic formula is stated at positive length `n+1`:
an empty cyclic-state product would not in general equal the trace of the identity.
-/

noncomputable section
namespace BilayerGap.HistoryCycles

open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Sum over all tuples by separating the first entry from the tail. -/
theorem sum_tuple_cons (n : ℕ) (f : (Fin (n+1) → ι) → ℝ) :
    (∑ v, f v) = ∑ i : ι, ∑ v : Fin n → ι, f (Fin.cons i v) := by
  calc
    (∑ v, f v) = ∑ p : ι × (Fin n → ι), f (Fin.cons p.1 p.2) :=
      ((Fin.consEquiv (fun _ : Fin (n+1) => ι)).sum_comp f).symm
    _ = ∑ i : ι, ∑ v : Fin n → ι, f (Fin.cons i v) := Fintype.sum_prod_type _

/-- An open chain of n+1 matrix entries, with n intermediate states. -/
def chainWeight (A : Matrix ι ι ℝ) (i j : ι) {n : ℕ} (v : Fin n → ι) : ℝ :=
  ∏ k : Fin (n+1), A ((Fin.cons i v : Fin (n+1) → ι) k) ((Fin.snoc v j : Fin (n+1) → ι) k)

omit [Fintype ι] [DecidableEq ι] in
theorem chainWeight_cons (A : Matrix ι ι ℝ) (i j k : ι) (n : ℕ)
    (v : Fin n → ι) :
    chainWeight A i j (Fin.cons k v) = A i k * chainWeight A k j v := by
  unfold chainWeight
  rw [← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Every entry of a matrix power is the finite sum over open state chains. -/
theorem pow_entry_eq_chain_sum (A : Matrix ι ι ℝ) (n : ℕ) (i j : ι) :
    (A^(n+1)) i j = ∑ v : Fin n → ι, chainWeight A i j v := by
  induction n generalizing i j with
  | zero => simp [chainWeight, Fin.snoc]
  | succ n ih =>
    calc
      (A^(n+1+1)) i j = ∑ k : ι, ∑ v : Fin n → ι,
          A i k * chainWeight A k j v := by
        rw [pow_succ', Matrix.mul_apply]
        simp_rw [ih, Finset.mul_sum]
      _ = ∑ v : Fin (n+1) → ι, chainWeight A i j v := by
        rw [sum_tuple_cons]
        simp_rw [chainWeight_cons]

omit [Fintype ι] [DecidableEq ι] in
/-- Closing the endpoints produces precisely the modular successor cycle. -/
theorem closed_chain_eq_cycle (A : Matrix ι ι ℝ) (n : ℕ) (i : ι)
    (v : Fin n → ι) :
    chainWeight A i i v =
      ∏ k : Fin (n+1), A ((Fin.cons i v : Fin (n+1) → ι) k) ((Fin.cons i v : Fin (n+1) → ι) (k+1)) := by
  simp only [chainWeight, Fin.snoc_eq_cons_rotate, finRotate_succ_apply]

/-- Exact finite cyclic contraction formula for a positive matrix-power length. -/
theorem trace_pow_eq_cycle_sum (A : Matrix ι ι ℝ) (n : ℕ) :
    Matrix.trace (A^(n+1)) =
      ∑ v : Fin (n+1) → ι, ∏ k : Fin (n+1), A (v k) (v (k+1)) := by
  change (∑ i : ι, (A^(n+1)) i i) = _
  simp_rw [pow_entry_eq_chain_sum]
  rw [sum_tuple_cons]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro v _
  exact closed_chain_eq_cycle A n i v

/-- The same cyclic contraction, with the explicit permutation API. -/
theorem trace_pow_eq_rotate_sum (A : Matrix ι ι ℝ) (n : ℕ) :
    Matrix.trace (A^(n+1)) =
      ∑ v : Fin (n+1) → ι, ∏ k : Fin (n+1), A (v k) (v (finRotate (n+1) k)) := by
  simpa only [finRotate_succ_apply] using trace_pow_eq_cycle_sum A n

#print axioms trace_pow_eq_cycle_sum
#print axioms trace_pow_eq_rotate_sum
end BilayerGap.HistoryCycles

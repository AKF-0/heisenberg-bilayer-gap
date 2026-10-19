import Gap.HistoryEuler

/-!
# Matrix polynomials give genuine exponential product limits

The one-step map is an actual entrywise polynomial matrix. Its constant and
linear coefficients determine the product limit. Differentiation is performed
by finite sums of scalar polynomials times matrix units, so the proof uses the
matrix operator norm throughout rather than substituting a pointwise Pi norm.
-/

noncomputable section
namespace BilayerGap.HistoryMatrixPolynomial

open Filter Polynomial
open scoped Topology Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Entrywise evaluation of a finite matrix with real-polynomial entries. -/
def matrixEval (P : Matrix ι ι ℝ[X]) (x : ℝ) : Matrix ι ι ℝ :=
  fun i j => (P i j).eval x

/-- A coefficient matrix of the actual polynomial entries. -/
def matrixCoeff (P : Matrix ι ι ℝ[X]) (k : ℕ) : Matrix ι ι ℝ :=
  fun i j => (P i j).coeff k

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem matrixEval_zero (P : Matrix ι ι ℝ[X]) :
    matrixEval P 0 = matrixCoeff P 0 := by
  ext i j
  exact (Polynomial.coeff_zero_eq_eval_zero (P i j)).symm

omit [Nonempty ι] in
theorem matrix_eq_sum_smul_single (A : Matrix ι ι ℝ) :
    A = ∑ i, ∑ j, A i j • (Matrix.single i j 1 : Matrix ι ι ℝ) := by
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single A

omit [Nonempty ι] in
theorem matrixEval_eq_sum (P : Matrix ι ι ℝ[X]) (x : ℝ) :
    matrixEval P x = ∑ i, ∑ j, (P i j).eval x • (Matrix.single i j 1 : Matrix ι ι ℝ) :=
  matrix_eq_sum_smul_single (matrixEval P x)

omit [Nonempty ι] in
theorem matrixCoeff_eq_sum (P : Matrix ι ι ℝ[X]) (k : ℕ) :
    matrixCoeff P k = ∑ i, ∑ j, (P i j).coeff k • (Matrix.single i j 1 : Matrix ι ι ℝ) :=
  matrix_eq_sum_smul_single (matrixCoeff P k)

omit [Nonempty ι] in
/-- Differentiability in the matrix operator norm, with the true linear coefficient. -/
theorem hasDerivAt_matrixEval_zero (P : Matrix ι ι ℝ[X]) :
    HasDerivAt (matrixEval P) (matrixCoeff P 1) 0 := by
  have hscalar (i j : ι) : HasDerivAt (fun x => (P i j).eval x) ((P i j).coeff 1) 0 := by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
      Nat.cast_zero, zero_add, mul_one] using (P i j).hasDerivAt (0:ℝ)
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (hscalar i j).smul_const (Matrix.single i j 1 : Matrix ι ι ℝ)))
  simpa only [← matrixEval_eq_sum, ← matrixCoeff_eq_sum] using h

omit [Nonempty ι] in
/-- Rescale time by any real beta; positivity is not needed for this matrix identity. -/
theorem hasDerivAt_matrixEval_scaled (P : Matrix ι ι ℝ[X]) (beta : ℝ) :
    HasDerivAt (fun t => matrixEval P (beta*t)) (beta • matrixCoeff P 1) 0 := by
  have ho : HasDerivAt (matrixEval P) (matrixCoeff P 1) (beta*(0:ℝ)) := by
    simpa only [mul_zero] using hasDerivAt_matrixEval_zero P
  have h := ho.scomp (0:ℝ) ((hasDerivAt_id (0:ℝ)).const_mul beta)
  simpa only [Function.comp_def, id_eq, mul_one] using h

/-- A matrix polynomial with constant coefficient I converges, under repeated
reciprocal-time steps, to the exponential of its linear coefficient. -/
theorem tendsto_pow_matrixEval (P : Matrix ι ι ℝ[X])
    (h0 : matrixCoeff P 0 = 1) (beta : ℝ) :
    Tendsto (fun (n : ℕ) => (matrixEval P (beta/((n:ℝ)+1)))^(n+1))
      atTop (𝓝 (NormedSpace.exp ℝ (beta • matrixCoeff P 1))) := by
  have hz : matrixEval P (beta*(0:ℝ)) = 1 := by
    rw [mul_zero, matrixEval_zero, h0]
  have h := History.tendsto_pow_of_hasDerivAt
    (fun t => matrixEval P (beta*t)) (beta • matrixCoeff P 1) hz
    (hasDerivAt_matrixEval_scaled P beta)
  simpa only [div_eq_mul_inv, one_div, one_mul] using h

#print axioms hasDerivAt_matrixEval_zero
#print axioms tendsto_pow_matrixEval
end BilayerGap.HistoryMatrixPolynomial

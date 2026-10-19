import Gap.HistoryPolynomial
import Gap.HistoryMatrixPolynomial
import Gap.FiniteMomentLimits

/-!
# A constructive finite symmetric transfer approximation

The transfer matrices below are explicit finite signed matrices. Their trace
moments converge to the exponential of an explicitly computed local strip
generator. Neither a compact-operator spectral theorem nor a model-to-transfer
convergence premise is used. The separate identification of column and bond
lifts with the concrete two-dimensional bilayer remains a geometry task.
-/
noncomputable section
namespace BilayerGap.History
open Filter
open scoped Topology Matrix.Norms.Operator
open HistoryMatrixPolynomial

variable {V B : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype B] [DecidableEq B]

/-- The exact generator determined by the on-site and single-bond sectors. -/
def stripGenerator (L : ℕ) (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (g : ℝ) :
    Matrix (Fin L → V) (Fin L → V) ℝ :=
  -onSiteGenerator h+g • oneEventGenerator (finRotate L) G

/-- The physical trace associated with that explicit finite strip generator. -/
def stripPartition (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (g β : ℝ) (L : ℕ) : ℝ :=
  Matrix.trace (NormedSpace.exp ℝ (β • stripGenerator L h G g))

/-- One finite transfer for each positive time resolution; importantly no
spatial length occurs among its arguments or in its finite state type. -/
def transferApprox (h : Matrix V V ℝ) (G : B → Matrix V V ℝ) (g β : ℝ) (q : ℕ) :
    Matrix (Fin (q+1) → Option B) (Fin (q+1) → Option B) ℝ :=
  collisionTransfer (finRotate (q+1)) h G (β/((q:ℝ)+1)) g

theorem transferApprox_symmetric (h : Matrix V V ℝ) (G : B → Matrix V V ℝ)
    (g β : ℝ) (q : ℕ) : (transferApprox h G g β q).IsSymm :=
  collisionTransfer_symmetric _ _ _ _ _

/-- The transfer trace converges for each fixed positive circumference, with
the same approximating matrix sequence for every circumference. -/
theorem transferApprox_trace_limit (h : Matrix V V ℝ) (G : B → Matrix V V ℝ)
    (g β : ℝ) (hg : 0 ≤ g) (hβ : 0 ≤ β) (L : ℕ) (hL : 0 < L) :
    Tendsto (fun q => Matrix.trace ((transferApprox h G g β q)^L)) atTop
      (𝓝 (stripPartition h G g β L)) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hL)
  let P := matchingPolynomial (finRotate (l+1)) h G g
  have hzero : matrixCoeff P 0 = 1 := matchingPolynomial_coeff_zero _ _ _ _
  have hlin : matrixCoeff P 1 = stripGenerator (l+1) h G g :=
    matchingPolynomial_coeff_one _ _ _ _
  have hp := tendsto_pow_matrixEval P hzero β
  have htrace : Continuous (Matrix.trace : Matrix (Fin (l+1) → V) (Fin (l+1) → V) ℝ → ℝ) := by
    unfold Matrix.trace
    fun_prop
  have hh := htrace.continuousAt.tendsto.comp hp
  rw [hlin] at hh
  change Tendsto _ atTop (𝓝 (stripPartition h G g β (l+1))) at hh
  apply hh.congr'
  apply Filter.Eventually.of_forall
  intro q
  unfold transferApprox collisionTransfer
  change Matrix.trace ((matrixEval P (β/((q:ℝ)+1)))^(q+1)) =
    Matrix.trace ((spatialKernel (finRotate (q+1))
      (collisionVertex h G (β/((q:ℝ)+1)) g))^(l+1))
  rw [trace_powers_space_time_exchange_rotate]
  have hv := temporalKernel_eq_eval_matchingPolynomial (finRotate (l+1)) h G
    (β/((q:ℝ)+1)) g (mul_nonneg (div_nonneg hβ (by positivity)) hg)
  rw [hv]
  rfl

/-- Real symmetry is precisely Hermitian symmetry over the real field. -/
theorem transferApprox_hermitian (h : Matrix V V ℝ) (G : B → Matrix V V ℝ)
    (g β : ℝ) (q : ℕ) : (transferApprox h G g β q).IsHermitian := by
  change (transferApprox h G g β q).conjTranspose = transferApprox h G g β q
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (transferApprox_symmetric h G g β q).eq

/-- Reindexing into Fin-cardinal coordinates does not change any trace moment. -/
theorem trace_reindex_pow {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℝ) (n : ℕ) :
    Matrix.trace (((Matrix.reindexAlgEquiv ℝ ℝ e) A)^n) = Matrix.trace (A^n) := by
  rw [← map_pow]
  change (∑ j, (A^n) (e.symm j) (e.symm j)) = ∑ i, (A^n) i i
  exact Equiv.sum_comp e.symm (fun i => (A^n) i i)

/-- The finite-spectral criterion's approximation hypothesis is now
constructed, not postulated, for the explicit strip generator. -/
def stripTransferLimit (h : Matrix V V ℝ) (G : B → Matrix V V ℝ)
    (g β : ℝ) (hg : 0 ≤ g) (hβ : 0 ≤ β) :
    FiniteSymmetricTransferLimit (stripPartition h G g β) := by
  classical
  refine {
    dim := fun q => Fintype.card (Fin (q+1) → Option B)
    transfer := fun q => (Matrix.reindexAlgEquiv ℝ ℝ
      (Fintype.equivFin (Fin (q+1) → Option B))) (transferApprox h G g β q)
    symmetric := ?_
    trace_limit := ?_
  }
  · intro q
    change ((transferApprox h G g β q).submatrix
      (Fintype.equivFin (Fin (q+1) → Option B)).symm
      (Fintype.equivFin (Fin (q+1) → Option B)).symm).IsHermitian
    exact (transferApprox_hermitian h G g β q).submatrix _
  · intro n hn
    have hlim := transferApprox_trace_limit h G g β hg hβ n hn.pos
    apply hlim.congr'
    exact Filter.Eventually.of_forall (fun q => (trace_reindex_pow _ _ _).symm)

#print axioms stripTransferLimit
#print axioms transferApprox_trace_limit
end BilayerGap.History

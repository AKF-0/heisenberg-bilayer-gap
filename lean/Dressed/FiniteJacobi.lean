import Dressed.HermitianInterlacing

/-!
# Finite Jacobi lower bounds by bidiagonal Gram factorization

All matrices in this file have a finite occupation cutoff. In particular,
only the leading principal block of the reversed Gram matrix has the shifted
Jacobi form: its final row is never silently supplied with a missing entry.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FiniteJacobi
open Matrix
set_option maxHeartbeats 800000

/-- A weighted strict upper shift. -/
def upperShift (n : ℕ) (u : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.val + 1 = j.val then u j.val else 0

/-- Upper bidiagonal matrix with diagonal `d` and upper diagonal `u`. -/
def bidiagonal (n : ℕ) (d u : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => d i.val) + upperShift n u

/-- Explicit tridiagonal matrix. The lower off-diagonal reuses the upper one. -/
def tridiagonal (n : ℕ) (d u : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => d i.val) + upperShift n u + (upperShift n u)ᵀ

@[simp] theorem upperShift_apply (n : ℕ) (u : ℕ → ℝ) (i j : Fin n) :
    upperShift n u i j = if i.val + 1 = j.val then u j.val else 0 := rfl

theorem upperShift_transpose_mul (n : ℕ) (u : ℕ → ℝ) :
    (upperShift n u)ᵀ * upperShift n u =
      diagonal (fun i : Fin n => if i.val = 0 then 0 else (u i.val)^2) := by
  ext i j
  simp only [mul_apply, transpose_apply, upperShift_apply, diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    by_cases hi : i.val = 0
    · simp only [hi, ite_true]
      apply Finset.sum_eq_zero
      intro k _
      simp
    · rw [if_neg hi]
      let p : Fin n := ⟨i.val - 1, by omega⟩
      rw [Finset.sum_eq_single p]
      · have hp : p.val + 1 = i.val := by dsimp [p]; omega
        simp [hp, pow_two]
      · intro k _ hkp
        have hk : k.val + 1 ≠ i.val := by
          intro hk
          apply hkp
          apply Fin.ext
          dsimp [p]
          omega
        simp [hk]
      · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k.val + 1 = i.val
    · have hkj : k.val + 1 ≠ j.val := by
        intro hkj
        apply hij
        exact Fin.ext (hki.symm.trans hkj)
      simp [hkj]
    · simp [hki]

theorem upperShift_mul_transpose (n : ℕ) (u : ℕ → ℝ) :
    upperShift n u * (upperShift n u)ᵀ =
      diagonal (fun i : Fin n => if i.val + 1 < n then (u (i.val + 1))^2 else 0) := by
  ext i j
  simp only [mul_apply, transpose_apply, upperShift_apply, diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    by_cases hi : i.val + 1 < n
    · rw [if_pos hi]
      let p : Fin n := ⟨i.val + 1, hi⟩
      rw [Finset.sum_eq_single p]
      · simp [p, pow_two]
      · intro k _ hkp
        have hk : i.val + 1 ≠ k.val := by
          intro hk
          apply hkp
          exact Fin.ext hk.symm
        simp [hk]
      · simp
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro k _
      have hk : i.val + 1 ≠ k.val := by omega
      simp [hk]
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i.val + 1 = k.val
    · have hjk : j.val + 1 ≠ k.val := by
        intro hjk
        apply hij
        apply Fin.ext
        omega
      simp [hjk]
    · simp [hik]

/-- Exact finite column-Gram calculation, including the first-column boundary. -/
theorem bidiagonal_transpose_mul (n : ℕ) (d u : ℕ → ℝ) :
    (bidiagonal n d u)ᵀ * bidiagonal n d u =
      tridiagonal n (fun i => (d i)^2 + if i = 0 then 0 else (u i)^2)
        (fun j => d (j-1) * u j) := by
  rw [bidiagonal, transpose_add, diagonal_transpose, add_mul, mul_add, mul_add,
    upperShift_transpose_mul]
  ext i j
  simp only [add_apply, tridiagonal, diagonal_mul_diagonal, diagonal_mul, mul_diagonal,
    diagonal_apply, upperShift_apply, transpose_apply]
  by_cases hij : i = j
  · subst j
    have hi : ¬ i.val + 1 = i.val := by omega
    simp [hi, pow_two]
  · have hji : j ≠ i := Ne.symm hij
    by_cases hu : i.val + 1 = j.val
    · have hv : ¬ j.val + 1 = i.val := by omega
      have hj : j.val - 1 = i.val := by omega
      simp [hij, hji, hu, hv, hj, pow_two]
    · by_cases hv : j.val + 1 = i.val
      · have hi : i.val - 1 = j.val := by omega
        simp [hij, hji, hu, hv, hi, pow_two, mul_comm]
      · simp [hij, hji, hu, hv]

/-- Exact leading row-Gram calculation. Only this leading block has every
upper-diagonal contribution; the last row of the full matrix does not. -/
theorem bidiagonal_mul_transpose_leading (n : ℕ) (d u : ℕ → ℝ) :
    ((bidiagonal (n+1) d u) * (bidiagonal (n+1) d u)ᵀ).submatrix
        Fin.castSucc Fin.castSucc =
      tridiagonal n (fun i => (d i)^2 + (u (i+1))^2)
        (fun j => u j * d j) := by
  rw [bidiagonal, transpose_add, diagonal_transpose, add_mul, mul_add, mul_add,
    upperShift_mul_transpose]
  ext i j
  simp only [submatrix_apply, add_apply, tridiagonal, diagonal_mul_diagonal,
    diagonal_mul, mul_diagonal, diagonal_apply, upperShift_apply, transpose_apply,
    Fin.coe_castSucc, Fin.castSucc_inj]
  have htop : i.val + 1 < n + 1 := by omega
  by_cases hij : i = j
  · subst j
    have hi : ¬ i.val + 1 = i.val := by omega
    simp [hi, htop, pow_two]
  · have hji : j ≠ i := Ne.symm hij
    by_cases hu : i.val + 1 = j.val
    · have hv : ¬ j.val + 1 = i.val := by omega
      simp [hij, hji, hu, hv, htop]
    · by_cases hv : j.val + 1 = i.val
      · simp [hij, hji, hu, hv, htop, mul_comm]
      · simp [hij, hji, hu, hv, htop]

/-- The finite Jacobi matrix from the oscillator parity problem. -/
def jacobi (n : ℕ) (b s t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  tridiagonal n (fun i => (s+t)*(i:ℝ)+s*b)
    (fun j => -Real.sqrt (s*t*(j:ℝ)*((j-1:ℕ)+b)))

/-- The displayed Jacobi diagonal is exactly `(s+t)i+sb`. -/
@[simp] theorem jacobi_diagonal (n : ℕ) (b s t : ℝ) (i : Fin n) :
    jacobi n b s t i i = (s+t)*(i.val:ℝ)+s*b := by
  simp [jacobi, tridiagonal]

/-- The adjacent entry has the standard square-root normalization. -/
theorem jacobi_adjacent (n : ℕ) (b s t : ℝ) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    jacobi n b s t i j = -Real.sqrt (s*t*((i.val:ℝ)+1)*((i.val:ℝ)+b)) := by
  have hne : i ≠ j := by intro h; subst j; omega
  have hji : j.val + 1 ≠ i.val := by omega
  have hj : j.val - 1 = i.val := by omega
  simp only [jacobi, tridiagonal, add_apply, diagonal_apply, if_neg hne,
    upperShift_apply, if_pos hij, transpose_apply, if_neg hji, zero_add, add_zero]
  rw [hj, ← hij, Nat.cast_add, Nat.cast_one]

/-- Nonadjacent off-diagonal entries vanish. -/
theorem jacobi_off_band (n : ℕ) (b s t : ℝ) (i j : Fin n)
    (hne : i ≠ j) (hu : i.val + 1 ≠ j.val) (hl : j.val + 1 ≠ i.val) :
    jacobi n b s t i j = 0 := by
  simp [jacobi, tridiagonal, hne, hu, hl]

/-- Its explicit finite upper-bidiagonal Gram factor. -/
def gramFactor (n : ℕ) (b s t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  bidiagonal n (fun i => Real.sqrt (s*((i:ℝ)+b)))
    (fun j => -Real.sqrt (t*(j:ℝ)))

/-- Exact Gram factorization, valid also at zero parameters. -/
theorem gramFactor_transpose_mul (n : ℕ) (b s t : ℝ)
    (hb : 0 ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (gramFactor n b s t)ᵀ * gramFactor n b s t = jacobi n b s t := by
  rw [gramFactor, bidiagonal_transpose_mul]
  have hd : (fun i : ℕ => Real.sqrt (s*((i:ℝ)+b)) ^ 2 +
      if i = 0 then 0 else (-Real.sqrt (t*(i:ℝ)))^2) =
      (fun i : ℕ => (s+t)*(i:ℝ)+s*b) := by
    funext i
    rw [Real.sq_sqrt (mul_nonneg hs (add_nonneg (Nat.cast_nonneg i) hb))]
    by_cases hi : i = 0
    · simp [hi]
    · rw [if_neg hi, neg_sq, Real.sq_sqrt (mul_nonneg ht (Nat.cast_nonneg i))]
      ring
  have hu : (fun j : ℕ => Real.sqrt (s*((j-1:ℕ)+b)) * (-Real.sqrt (t*(j:ℝ)))) =
      (fun j : ℕ => -Real.sqrt (s*t*(j:ℝ)*((j-1:ℕ)+b))) := by
    funext j
    rw [mul_neg, ← Real.sqrt_mul (mul_nonneg hs (add_nonneg (Nat.cast_nonneg _) hb))]
    congr 2
    ring
  rw [hd, hu]
  rfl

/-- Positivity follows from the actual factor, not from a spectral assumption. -/
theorem jacobi_posSemidef (n : ℕ) (b s t : ℝ)
    (hb : 0 ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (jacobi n b s t).PosSemidef := by
  rw [← gramFactor_transpose_mul n b s t hb hs ht]
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    posSemidef_conjTranspose_mul_self (gramFactor n b s t)

/-- Shape invariance holds on the leading principal block, not the whole
row-Gram matrix. This statement records the finite top-cutoff correction. -/
theorem gramFactor_mul_transpose_leading (n : ℕ) (b s t : ℝ)
    (hb : 0 ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ((gramFactor (n+1) b s t) * (gramFactor (n+1) b s t)ᵀ).submatrix
        Fin.castSucc Fin.castSucc =
      jacobi n (b+1) s t + (t-s) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [gramFactor, bidiagonal_mul_transpose_leading]
  have hd (i : ℕ) : Real.sqrt (s*((i:ℝ)+b))^2 +
      (-Real.sqrt (t*((i+1:ℕ):ℝ)))^2 =
      (s+t)*(i:ℝ)+s*(b+1)+(t-s) := by
    rw [Real.sq_sqrt (mul_nonneg hs (add_nonneg (Nat.cast_nonneg i) hb)),
      neg_sq, Real.sq_sqrt (mul_nonneg ht (Nat.cast_nonneg _))]
    push_cast
    ring
  have hu (j : ℕ) : (-Real.sqrt (t*(j:ℝ))) * Real.sqrt (s*((j:ℝ)+b)) =
      -Real.sqrt (s*t*(j:ℝ)*((j-1:ℕ)+(b+1))) := by
    rw [neg_mul, ← Real.sqrt_mul (mul_nonneg ht (Nat.cast_nonneg _))]
    congr 2
    cases j with
    | zero => simp
    | succ j => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]; ring
  ext i j
  simp only [tridiagonal, jacobi, add_apply, diagonal_apply, upperShift_apply,
    transpose_apply, smul_apply, smul_eq_mul, one_apply]
  simp only [hu]
  by_cases hij : i = j
  · subst j
    have hi : i.val + 1 ≠ i.val := by omega
    simp only [if_true, if_neg hi, add_zero, mul_one]
    exact hd i.val
  · simp only [if_neg hij, zero_add, mul_zero, add_zero]

/-- Actual decreasing eigenvalues with the natural `Fin n` index type. -/
def descendingValue {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (k : Fin n) : ℝ :=
  hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k)

theorem descendingValue_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (k : Fin n) : 0 ≤ descendingValue hA.1 k := by
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have h := hA.eigenvalues_nonneg (e (Fin.cast (Fintype.card_fin n).symm k))
  simpa [Matrix.IsHermitian.eigenvalues, descendingValue, e] using h

/-- Actual sorted-spectrum recurrence obtained from shape invariance and
finite principal-block interlacing. -/
theorem descendingValue_recurrence (n : ℕ) (b s t : ℝ)
    (hb : 0 ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t) (k : Fin n) :
    (t-s) + descendingValue (jacobi_posSemidef n (b+1) s t (by linarith) hs ht).1 k ≤
      descendingValue (jacobi_posSemidef (n+1) b s t hb hs ht).1 k.castSucc := by
  let A := gramFactor (n+1) b s t
  let B := A * Aᵀ
  have hB : B.IsHermitian := by
    simpa only [B, conjTranspose_eq_transpose_of_trivial] using
      (posSemidef_self_mul_conjTranspose A).1
  let C := B.submatrix Fin.castSucc Fin.castSucc
  have hC : C.IsHermitian := hB.submatrix Fin.castSucc
  have hL := (jacobi_posSemidef n (b+1) s t (by linarith) hs ht).1
  have hLC : C = jacobi n (b+1) s t + (t-s) • (1 : Matrix (Fin n) (Fin n) ℝ) :=
    gramFactor_mul_transpose_leading n b s t hb hs ht
  have hform (x : EuclideanSpace ℝ (Fin n)) :
      1 * ⟪x, (jacobi n (b+1) s t).toEuclideanLin x⟫ - (-(t-s)) * ‖x‖^2 ≤
        ⟪x, C.toEuclideanLin x⟫ := by
    rw [hLC]
    simp [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
      Matrix.toEuclideanLin_apply]
    <;> ring_nf
    exact le_rfl
  have hshift := symmetric_eigenvalues_affine_lower
    (jacobi n (b+1) s t).toEuclideanLin C.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hL)
    (Matrix.isHermitian_iff_isSymmetric.mp hC) finrank_euclideanSpace
    1 (-(t-s)) (by norm_num) hform (Fin.cast (Fintype.card_fin n).symm k)
  have hinter := hermitian_leading_eigenvalues₀_le B hB k
  have hspec : (jacobi_posSemidef (n+1) b s t hb hs ht).1.eigenvalues₀ =
      hB.eigenvalues₀ := by
    apply hermitian_eigenvalues₀_eq_of_charpoly_eq
    rw [← gramFactor_transpose_mul (n+1) b s t hb hs ht]
    exact charpoly_mul_comm _ _
  change 1 * hL.eigenvalues₀ _ - (-(t-s)) ≤ hC.eigenvalues₀ _ at hshift
  unfold descendingValue
  rw [hspec]
  linarith

/-- The kth decreasing eigenvalue is at least `(t-s)(n-1-k)`.
The induction uses no positivity or invertibility beyond the displayed
nonnegative radicands; in particular zero `s` and zero `b` are included. -/
theorem descendingValue_lower (n : ℕ) (b s t : ℝ)
    (hb : 0 ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t) (k : Fin n) :
    (t-s) * ((n-1-k.val:ℕ):ℝ) ≤
      descendingValue (jacobi_posSemidef n b s t hb hs ht).1 k := by
  induction n generalizing b with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      by_cases hk : k.val < n
      · let j : Fin n := ⟨k.val, hk⟩
        have hrec := descendingValue_recurrence n b s t hb hs ht j
        have hind := ih (b+1) (by linarith) j
        have heq : j.castSucc = k := Fin.ext rfl
        rw [heq] at hrec
        have hnat : n + 1 - 1 - k.val = (n - 1 - j.val) + 1 := by
          dsimp [j]
          omega
        rw [hnat, Nat.cast_add, Nat.cast_one]
        nlinarith
      · have hk' : n + 1 - 1 - k.val = 0 := by omega
        rw [hk', Nat.cast_zero, mul_zero]
        exact descendingValue_nonneg (jacobi_posSemidef (n+1) b s t hb hs ht) k

/-- Main finite Jacobi spectral lemma: the actual increasingly sorted jth
eigenvalue is at least `(t-s)j`, with all multiplicities retained. -/
theorem ascendingEigenvalue_lower (n : ℕ) (b s t : ℝ)
    (hb : 0 ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t) (j : Fin n) :
    (t-s) * (j.val:ℝ) ≤
      ascendingEigenvalue (jacobi_posSemidef n b s t hb hs ht).1
        (Fin.cast (Fintype.card_fin n).symm j) := by
  have h := descendingValue_lower n b s t hb hs ht j.rev
  have hnat : n - 1 - j.rev.val = j.val := by
    have hj := j.isLt
    change n - 1 - (n - (j.val + 1)) = j.val
    omega
  rw [hnat] at h
  convert h using 1
  unfold descendingValue ascendingEigenvalue
  rw [Fin.cast_rev]

end BilayerDressed.FiniteJacobi

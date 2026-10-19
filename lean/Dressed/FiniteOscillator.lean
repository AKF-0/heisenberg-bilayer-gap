import Dressed.FiniteJacobi

/-!
# Concrete finite oscillator parity blocks

This module specializes the finite Jacobi bound to the actual tridiagonal
parity coefficients of a truncated single oscillator. Zero pairing is included.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FiniteOscillator
open Matrix FiniteJacobi
set_option maxHeartbeats 800000

/-- The frequency obtained by the stable scalar square root. -/
def frequency (ω z : ℝ) : ℝ := Real.sqrt (ω^2-z^2)

/-- The scalar reference energy. -/
def vacuumEnergy (ω z : ℝ) : ℝ := (frequency ω z-ω)/2

theorem stable_parameters (ω z : ℝ) (h : |z| < ω) :
    0 < frequency ω z ∧ 0 ≤ ω-frequency ω z ∧ 0 ≤ ω+frequency ω z ∧
      (ω-frequency ω z)*(ω+frequency ω z) = z^2 := by
  have hω : 0 < ω := lt_of_le_of_lt (abs_nonneg z) h
  have hr : 0 < ω^2-z^2 := by
    nlinarith [sq_abs z, mul_pos (sub_pos.mpr h) (show 0 < ω+|z| by positivity)]
  have hsq : (frequency ω z)^2 = ω^2-z^2 := Real.sq_sqrt hr.le
  have hΩ : 0 < frequency ω z := Real.sqrt_pos.mpr hr
  have hle : frequency ω z ≤ ω := by nlinarith [sq_nonneg z]
  exact ⟨hΩ, sub_nonneg.mpr hle, by linarith, by nlinarith⟩

/-- The parity-p occupation block, indexed by occupations `2i+p`.
Its upper entry is `z sqrt((i+1)(i+p+1/2))`. -/
def parityBlock (n : ℕ) (p ω z : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  tridiagonal n (fun i => ω*(2*(i:ℝ)+p))
    (fun j => z*Real.sqrt ((j:ℝ)*((j-1:ℕ)+p+1/2)))

theorem tridiagonal_hermitian (n : ℕ) (d u : ℕ → ℝ) :
    (tridiagonal n d u).IsHermitian := by
  unfold tridiagonal
  rw [add_assoc]
  apply (isHermitian_diagonal _).add
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    isHermitian_add_transpose_self (upperShift n u)

theorem parityBlock_hermitian (n : ℕ) (p ω z : ℝ) :
    (parityBlock n p ω z).IsHermitian := tridiagonal_hermitian _ _ _

/-- Exact identification of the negative-pairing block with the shifted
Jacobi matrix, before taking any spectral bound. -/
theorem negative_parityBlock_eq (n : ℕ) (p ω z : ℝ) (hp : 0 ≤ p)
    (h : |z| < ω) :
    parityBlock n p ω (-|z|) =
      jacobi n (p+1/2) (ω-frequency ω z) (ω+frequency ω z) +
        (vacuumEnergy ω z+p*frequency ω z) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨hΩ, hs, ht, hst⟩ := stable_parameters ω z h
  have hu (j : ℕ) :
      -Real.sqrt ((ω-frequency ω z)*(ω+frequency ω z)*(j:ℝ)*((j-1:ℕ)+(p+1/2))) =
        (-|z|)*Real.sqrt ((j:ℝ)*((j-1:ℕ)+p+1/2)) := by
    rw [hst]
    have heq : z^2*(j:ℝ)*((j-1:ℕ)+(p+1/2)) =
        z^2*((j:ℝ)*((j-1:ℕ)+p+1/2)) := by ring
    rw [heq, Real.sqrt_mul (sq_nonneg z), Real.sqrt_sq_eq_abs]
    ring
  ext i j
  simp only [parityBlock, jacobi, tridiagonal, add_apply, diagonal_apply,
    upperShift_apply, transpose_apply, smul_apply, smul_eq_mul, one_apply, hu]
  by_cases hij : i = j
  · subst j
    have hi : i.val + 1 ≠ i.val := by omega
    simp only [if_true, if_neg hi, add_zero, mul_one]
    unfold vacuumEnergy
    ring
  · simp only [if_neg hij, zero_add, mul_zero, add_zero]

/-- Alternating occupation signs remove the sign of a parity coupling. -/
def alternatingGauge (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => (-1:ℝ)^i.val)

theorem alternatingGauge_sq (n : ℕ) :
    alternatingGauge n * alternatingGauge n = 1 := by
  rw [alternatingGauge, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [diagonal_apply_eq, one_apply_eq]
    rw [← mul_pow]
    simp
  · simp [diagonal_apply, hij]

/-- Concrete sign-gauge identity for the full finite parity block. -/
theorem alternatingGauge_parityBlock (n : ℕ) (p ω z : ℝ) :
    alternatingGauge n * parityBlock n p ω z * alternatingGauge n =
      parityBlock n p ω (-z) := by
  ext i j
  simp only [alternatingGauge, diagonal_mul, mul_diagonal, parityBlock, tridiagonal,
    add_apply, diagonal_apply, upperShift_apply, transpose_apply]
  have hsq (k : ℕ) : (-1:ℝ)^k * (-1:ℝ)^k = 1 := by rw [← mul_pow]; simp
  have hpair (k : ℕ) (x : ℝ) : (-1:ℝ)^k*x*((-1:ℝ)^k*(-1)) = -x := by
    calc
      _ = -((-1:ℝ)^k * (-1:ℝ)^k)*x := by ring
      _ = _ := by rw [hsq]; ring
  by_cases hij : i = j
  · subst j
    have hi : i.val + 1 ≠ i.val := by omega
    simp only [if_true, if_neg hi, add_zero]
    calc
      (-1:ℝ)^i.val * (ω*(2*(i.val:ℝ)+p)) * (-1:ℝ)^i.val =
          ((-1:ℝ)^i.val * (-1:ℝ)^i.val) * (ω*(2*(i.val:ℝ)+p)) := by ring
      _ = _ := by rw [hsq, one_mul]
  · by_cases hu : i.val + 1 = j.val
    · have hl : j.val + 1 ≠ i.val := by omega
      simp only [if_neg hij, if_pos hu, if_neg hl, zero_add, add_zero]
      rw [← hu, pow_succ]
      simpa only [neg_mul] using hpair i.val (z * Real.sqrt (((i.val+1:ℕ):ℝ)*((i.val+1-1:ℕ)+p+1/2)))
    · by_cases hl : j.val + 1 = i.val
      · simp only [if_neg hij, if_neg hu, if_pos hl, zero_add, add_zero]
        rw [← hl, pow_succ]
        convert hpair j.val (z * Real.sqrt (((j.val+1:ℕ):ℝ)*((j.val+1-1:ℕ)+p+1/2))) using 1 <;> ring
      · simp [hij, hu, hl]

/-- Gauge conjugation preserves the actual finite ordered spectrum. -/
theorem parityBlock_neg_eigenvalues₀ (n : ℕ) (p ω z : ℝ) :
    (parityBlock_hermitian n p ω (-z)).eigenvalues₀ =
      (parityBlock_hermitian n p ω z).eigenvalues₀ := by
  apply hermitian_eigenvalues₀_eq_of_charpoly_eq
  rw [← alternatingGauge_parityBlock, charpoly_mul_comm,
    ← mul_assoc, alternatingGauge_sq, one_mul]

/-- Every actual parity eigenvalue has the expected finite oscillator lower
bound, for either sign of the pairing and including zero pairing. -/
theorem parityBlock_ascendingEigenvalue_lower (n : ℕ) (p ω z : ℝ)
    (hp : 0 ≤ p) (h : |z| < ω) (j : Fin n) :
    vacuumEnergy ω z + (2*(j.val:ℝ)+p)*frequency ω z ≤
      ascendingEigenvalue (parityBlock_hermitian n p ω z)
        (Fin.cast (Fintype.card_fin n).symm j) := by
  obtain ⟨hΩ, hs, ht, hst⟩ := stable_parameters ω z h
  have hb : 0 ≤ p+1/2 := by linarith
  let L := jacobi n (p+1/2) (ω-frequency ω z) (ω+frequency ω z)
  have hL : L.IsHermitian := (jacobi_posSemidef _ _ _ _ hb hs ht).1
  have hform (x : EuclideanSpace ℝ (Fin n)) :
      1 * ⟪x, L.toEuclideanLin x⟫ - (-(vacuumEnergy ω z+p*frequency ω z)) * ‖x‖^2 ≤
        ⟪x, (parityBlock n p ω (-|z|)).toEuclideanLin x⟫ := by
    rw [negative_parityBlock_eq n p ω z hp h]
    dsimp [L]
    simp [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
      Matrix.toEuclideanLin_apply]
    <;> ring_nf
    exact le_rfl
  have hshift := hermitian_ascendingEigenvalue_affine_lower
    L (parityBlock n p ω (-|z|)) hL (parityBlock_hermitian _ _ _ _)
    1 (-(vacuumEnergy ω z+p*frequency ω z)) (by norm_num) hform
    (Fin.cast (Fintype.card_fin n).symm j)
  have hbound := FiniteJacobi.ascendingEigenvalue_lower n (p+1/2)
    (ω-frequency ω z) (ω+frequency ω z) hb hs ht j
  have hsign : (parityBlock_hermitian n p ω (-|z|)).eigenvalues₀ =
      (parityBlock_hermitian n p ω z).eigenvalues₀ := by
    apply hermitian_eigenvalues₀_eq_of_charpoly_eq
    by_cases hz : z ≤ 0
    · rw [abs_of_nonpos hz, neg_neg]
    · rw [abs_of_pos (lt_of_not_ge hz), ← alternatingGauge_parityBlock,
        charpoly_mul_comm, ← mul_assoc, alternatingGauge_sq, one_mul]
  unfold ascendingEigenvalue at hshift ⊢
  rw [hsign] at hshift
  change (ω+frequency ω z-(ω-frequency ω z))*(j.val:ℝ) ≤
    ascendingEigenvalue hL (Fin.cast (Fintype.card_fin n).symm j) at hbound
  unfold ascendingEigenvalue at hbound
  linarith

/-- Pair creation/annihilation connects occupation levels two apart. -/
def pairUpper (m : ℕ) (z : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i.val+2 = j.val then
    (z/2)*Real.sqrt ((j.val:ℝ)*((j.val:ℝ)-1)) else 0

/-- The actual occupation-cutoff oscillator `ωN+(z/2)(a†²+a²)`,
with levels `0,...,m-1` and the top transitions deleted. -/
def occupationMatrix (m : ℕ) (ω z : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  diagonal (fun i => ω*(i.val:ℝ)) + pairUpper m z + (pairUpper m z)ᵀ

theorem occupationMatrix_hermitian (m : ℕ) (ω z : ℝ) :
    (occupationMatrix m ω z).IsHermitian := by
  unfold occupationMatrix
  rw [add_assoc]
  apply (isHermitian_diagonal _).add
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    isHermitian_add_transpose_self (pairUpper m z)

/-- Occupation indices for one parity sector, with an explicit cutoff bound. -/
def parityIndex (m n : ℕ) (p : Fin 2) (hcut : ∀ i : Fin n, 2*i.val+p.val < m)
    (i : Fin n) : Fin m := ⟨2*i.val+p.val, hcut i⟩

theorem parityIndex_injective (m n : ℕ) (p : Fin 2)
    (hcut : ∀ i : Fin n, 2*i.val+p.val < m) :
    Function.Injective (parityIndex m n p hcut) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  dsimp [parityIndex] at hval
  omega

theorem parity_pair_coefficient (p : Fin 2) (j : ℕ) (hj : 0 < j) (z : ℝ) :
    (z/2)*Real.sqrt (((2*j+p.val:ℕ):ℝ)*(((2*j+p.val:ℕ):ℝ)-1)) =
      z*Real.sqrt ((j:ℝ)*((j-1:ℕ)+(p.val:ℝ)+1/2)) := by
  have hjcast : ((j-1:ℕ):ℝ) = (j:ℝ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hrad : (((2*j+p.val:ℕ):ℝ)*(((2*j+p.val:ℕ):ℝ)-1)) =
      4*((j:ℝ)*((j-1:ℕ)+(p.val:ℝ)+1/2)) := by
    rw [hjcast]
    fin_cases p <;> push_cast <;> ring
  rw [hrad, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  norm_num
  ring

/-- Extracting either parity from the actual cutoff matrix gives exactly the
parity block to which the proved Jacobi theorem applies. -/
theorem occupationMatrix_parity_submatrix (m n : ℕ) (p : Fin 2)
    (hcut : ∀ i : Fin n, 2*i.val+p.val < m) (ω z : ℝ) :
    (occupationMatrix m ω z).submatrix (parityIndex m n p hcut)
      (parityIndex m n p hcut) = parityBlock n (p.val:ℝ) ω z := by
  ext i j
  have heq : parityIndex m n p hcut i = parityIndex m n p hcut j ↔ i = j :=
    (parityIndex_injective m n p hcut).eq_iff
  have hu : (2*i.val+p.val)+2 = 2*j.val+p.val ↔ i.val+1 = j.val := by omega
  have hl : (2*j.val+p.val)+2 = 2*i.val+p.val ↔ j.val+1 = i.val := by omega
  simp only [submatrix_apply, occupationMatrix, parityBlock, tridiagonal,
    add_apply, diagonal_apply, heq, pairUpper, transpose_apply, upperShift_apply]
  simp only [parityIndex, hu, hl]
  by_cases hij : i = j
  · subst j
    have hi : i.val+1 ≠ i.val := by omega
    simp [hi]
  · by_cases hu' : i.val+1 = j.val
    · have hl' : j.val+1 ≠ i.val := by omega
      simp only [if_neg hij, if_pos hu', if_neg hl', zero_add, add_zero]
      exact parity_pair_coefficient p j.val (by omega) z
    · by_cases hl' : j.val+1 = i.val
      · simp only [if_neg hij, if_neg hu', if_pos hl', zero_add, add_zero]
        exact parity_pair_coefficient p i.val (by omega) z
      · simp [hij, hu', hl']

/-- The standard finite annihilation matrix, with entry `sqrt(j)` from
occupation `j` to `j-1`. Its transpose is the finite creation matrix. -/
def annihilation (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  upperShift m (fun j => Real.sqrt (j:ℝ))

/-- Squaring the concrete truncated ladder operator gives the standard
pair-annihilation coefficients; no top-boundary commutator is asserted. -/
theorem annihilation_sq_apply (m : ℕ) (i j : Fin m) :
    (annihilation m * annihilation m) i j =
      if i.val+2 = j.val then Real.sqrt ((j.val:ℝ)*((j.val:ℝ)-1)) else 0 := by
  simp only [mul_apply, annihilation, upperShift_apply]
  by_cases hij : i.val+2 = j.val
  · rw [if_pos hij]
    let k : Fin m := ⟨i.val+1, by omega⟩
    rw [Finset.sum_eq_single k]
    · have hik : i.val+1 = k.val := rfl
      have hkj : k.val+1 = j.val := by dsimp [k]; omega
      rw [if_pos hik, if_pos hkj, ← Real.sqrt_mul (Nat.cast_nonneg k.val)]
      congr 1
      have heq : (k.val:ℝ) = (j.val:ℝ)-1 := by
        have hc : (k.val:ℝ)+1 = (j.val:ℝ) := by exact_mod_cast hkj
        linarith
      rw [heq]
      ring
    · intro l _ hl
      have hil : i.val+1 ≠ l.val := by
        intro h
        apply hl
        exact Fin.ext h.symm
      simp [hil]
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i.val+1 = k.val
    · have hkj : k.val+1 ≠ j.val := by omega
      simp [hkj]
    · simp [hik]

/-- The entry-defined cutoff is exactly the finite ladder-operator formula
`ωN + (z/2)(a²+(a†)²)`. This checks its physical normalization. -/
theorem occupationMatrix_eq_ladder_formula (m : ℕ) (ω z : ℝ) :
    occupationMatrix m ω z =
      ω • diagonal (fun i : Fin m => (i.val:ℝ)) +
        (z/2) • (annihilation m * annihilation m +
          (annihilation m)ᵀ * (annihilation m)ᵀ) := by
  rw [← transpose_mul]
  ext i j
  simp only [occupationMatrix, add_apply, diagonal_apply, pairUpper, transpose_apply,
    smul_apply, smul_eq_mul, annihilation_sq_apply]
  split_ifs <;> ring

end BilayerDressed.FiniteOscillator

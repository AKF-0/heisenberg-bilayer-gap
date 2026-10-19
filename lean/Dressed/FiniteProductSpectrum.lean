import Dressed.FiniteOscillatorSpectrum
import Gap.TorusLifts

/-!
# Actual finite products of heterogeneous Hermitian matrices

The tensor basis is a finite function type, and each operator is the actual
site lift with identities on all other factors. All product diagonalization
and spectral identities are proved from finite matrix entries.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.FiniteProduct
open Matrix BilayerGap
set_option maxHeartbeats 800000

variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

/-- Entrywise finite tensor product, with a heterogeneous local matrix at each mode. -/
def tensorMatrix (A : I → Matrix S S ℝ) : Matrix (I → S) (I → S) ℝ :=
  fun s t => ∏ i, A i (s i) (t i)

@[simp] theorem tensorMatrix_one :
    tensorMatrix (fun _ : I => (1 : Matrix S S ℝ)) = 1 := by
  classical
  ext s t
  simp only [tensorMatrix, Matrix.one_apply, Finset.prod_boole, Finset.mem_univ,
    forall_true_left]
  simp only [← funext_iff]

@[simp] theorem tensorMatrix_transpose (A : I → Matrix S S ℝ) :
    (tensorMatrix A).transpose = tensorMatrix (fun i => (A i).transpose) := rfl

/-- Finite Fubini is exactly multiplication of the actual tensor matrices. -/
theorem tensorMatrix_mul (A B : I → Matrix S S ℝ) :
    tensorMatrix A * tensorMatrix B = tensorMatrix (fun i => A i * B i) := by
  classical
  ext s t
  simp only [Matrix.mul_apply, tensorMatrix, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => A i (s i) j * B i j (t i))).symm

/-- The matrix tensor product of one local matrix and identities is the
existing concrete site-lift operator, not a replacement abstraction. -/
theorem tensorMatrix_single (A : Matrix S S ℝ) (v : I) :
    tensorMatrix (Function.update (fun _ : I => (1 : Matrix S S ℝ)) v A) =
      Torus.siteLift A v := by
  classical
  ext s t
  rw [Torus.siteLift_eq_delta_product]
  unfold tensorMatrix
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rfl

/-- Local orthogonal matrices give a genuine orthogonal tensor basis. -/
theorem tensorMatrix_orthogonal (Q : I → Matrix S S ℝ)
    (hQ : ∀ i, (Q i).transpose * Q i = 1) :
    (tensorMatrix Q).transpose * tensorMatrix Q = 1 := by
  rw [tensorMatrix_transpose, tensorMatrix_mul]
  simp only [hQ, tensorMatrix_one]

/-- Conjugation of an actual site lift acts only on that local factor. -/
theorem tensorMatrix_conjugate_siteLift (Q : I → Matrix S S ℝ)
    (hQ : ∀ i, (Q i).transpose * Q i = 1) (A : Matrix S S ℝ) (v : I) :
    (tensorMatrix Q).transpose * Torus.siteLift A v * tensorMatrix Q =
      Torus.siteLift ((Q v).transpose * A * Q v) v := by
  rw [← tensorMatrix_single, tensorMatrix_transpose, tensorMatrix_mul, tensorMatrix_mul,
    ← tensorMatrix_single]
  congr 1
  funext i
  by_cases hi : i = v
  · subst i
    simp
  · simp [Function.update_of_ne hi, hQ i]

/-- Genuine sum of local Hamiltonians on the product configuration space. -/
def hamiltonian (A : I → Matrix S S ℝ) : Matrix (I → S) (I → S) ℝ :=
  ∑ i, Torus.siteLift (A i) i

theorem hamiltonian_hermitian (A : I → Matrix S S ℝ)
    (hA : ∀ i, (A i).IsHermitian) : (hamiltonian A).IsHermitian := by
  unfold Matrix.IsHermitian hamiltonian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun i _ => Torus.siteLift_hermitian (A i) (hA i) i)

/-- Arbitrary diagonal local matrices remain diagonal under the actual lift. -/
theorem siteLift_diagonal (d : S → ℝ) (v : I) :
    Torus.siteLift (Matrix.diagonal d) v =
      Matrix.diagonal (fun s : I → S => d (s v)) := by
  classical
  ext s t
  by_cases hst : s = t
  · subst t
    simp [Torus.siteLift]
  · have h : ¬ ((∀ w, w ≠ v → s w = t w) ∧ s v = t v) := by
      intro hh
      apply hst
      funext w
      by_cases hw : w = v
      · simpa [hw] using hh.2
      · exact hh.1 w hw
    simp only [Torus.siteLift, Matrix.diagonal_apply, hst, if_false]
    split_ifs with hout hv <;> simp_all

/-- Local diagonal data add exactly on the finite product basis. -/
theorem hamiltonian_diagonal (d : I → S → ℝ) :
    hamiltonian (fun i => diagonal (d i)) = diagonal (fun s => ∑ i, d i (s i)) := by
  unfold hamiltonian
  simp_rw [siteLift_diagonal]
  ext s t
  by_cases hst : s = t <;> simp [Matrix.sum_apply, Matrix.diagonal_apply, hst]

/-- Actual tensor change-of-basis formula for arbitrary local diagonalizations. -/
theorem tensorMatrix_diagonalization (A Q : I → Matrix S S ℝ) (d : I → S → ℝ)
    (hQ : ∀ i, (Q i).transpose * Q i = 1)
    (hdiag : ∀ i, (Q i).transpose * A i * Q i = diagonal (d i)) :
    (tensorMatrix Q).transpose * hamiltonian A * tensorMatrix Q =
      diagonal (fun s => ∑ i, d i (s i)) := by
  unfold hamiltonian
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [tensorMatrix_conjugate_siteLift Q hQ, hdiag]
  exact hamiltonian_diagonal d

/-- Canonical permutation taking increasing indices to mathlib's local eigenbasis labels. -/
def increasingOrder (m : ℕ) : Fin m ≃ Fin m :=
  ((finCongr (Fintype.card_fin m).symm).trans Fin.revPerm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m))))

/-- The actual local spectral matrix, with its columns increasingly ordered. -/
def increasingMatrix {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : Matrix (Fin m) (Fin m) ℝ :=
  (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ).submatrix id (increasingOrder m)

theorem increasingMatrix_orthogonal {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : (increasingMatrix hA).transpose * increasingMatrix hA = 1 := by
  let Q : Matrix (Fin m) (Fin m) ℝ := hA.eigenvectorUnitary
  have hQ : Q.transpose * Q = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using unitary.coe_star_mul_self hA.eigenvectorUnitary
  change (Q.submatrix id (increasingOrder m)).transpose *
    Q.submatrix id (increasingOrder m) = 1
  rw [Matrix.transpose_submatrix]
  rw [← Matrix.submatrix_mul Q.transpose Q (increasingOrder m) id (increasingOrder m) Function.bijective_id, hQ]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply, (increasingOrder m).injective.eq_iff]

/-- Increasing columns diagonalize the actual local matrix. -/
theorem increasingMatrix_diagonalization {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) :
    (increasingMatrix hA).transpose * A * increasingMatrix hA =
      diagonal (FiniteOscillator.increasingValue hA) := by
  let Q : Matrix (Fin m) (Fin m) ℝ := hA.eigenvectorUnitary
  have hdiag : Q.transpose * A * Q = diagonal hA.eigenvalues := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.id_comp] using hA.star_mul_self_mul_eq_diagonal
  have hprod : (increasingMatrix hA).transpose * A * increasingMatrix hA =
      (Q.transpose * A * Q).submatrix (increasingOrder m) (increasingOrder m) := by
    change (Q.submatrix id (increasingOrder m)).transpose * A *
      Q.submatrix id (increasingOrder m) = _
    rw [Matrix.transpose_submatrix]
    conv_lhs => arg 1; arg 2; rw [← Matrix.submatrix_id_id A]
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
  rw [hprod, hdiag]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply,
    (increasingOrder m).injective.eq_iff]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, Matrix.IsHermitian.eigenvalues, increasingOrder,
      Equiv.trans_apply, Equiv.symm_apply_apply, FiniteOscillator.increasingValue,
      ascendingEigenvalue]
    rfl
  · simp [hij]

/-- Tensor product of the actual increasing local eigenbases. -/
def spectralMatrix {m : ℕ} (A : I → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (A i).IsHermitian) : Matrix (I → Fin m) (I → Fin m) ℝ :=
  tensorMatrix (fun i => increasingMatrix (hA i))

/-- The product eigenvalue label records the sum of actual local eigenvalues. -/
def spectralEnergy {m : ℕ} (A : I → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (s : I → Fin m) : ℝ :=
  ∑ i, FiniteOscillator.increasingValue (hA i) (s i)

theorem spectralMatrix_orthogonal {m : ℕ} (A : I → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    (spectralMatrix A hA).transpose * spectralMatrix A hA = 1 :=
  tensorMatrix_orthogonal _ (fun i => increasingMatrix_orthogonal (hA i))

/-- Full actual product diagonalization, including all spectral multiplicities. -/
theorem spectralMatrix_diagonalization {m : ℕ} (A : I → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    (spectralMatrix A hA).transpose * hamiltonian A * spectralMatrix A hA =
      diagonal (spectralEnergy A hA) :=
  tensorMatrix_diagonalization _ _ _ (fun i => increasingMatrix_orthogonal (hA i))
    (fun i => increasingMatrix_diagonalization (hA i))

/-- Equality of characteristic polynomials, rather than merely spectral sets. -/
theorem hamiltonian_charpoly {m : ℕ} (A : I → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    (hamiltonian A).charpoly = (diagonal (spectralEnergy A hA)).charpoly := by
  rw [← spectralMatrix_diagonalization A hA,
    Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Matrix.mul_eq_one_comm.mp (spectralMatrix_orthogonal A hA), Matrix.one_mul]

/-- Any spectral function can be summed over the concrete product energy labels. -/
theorem sum_ascendingEigenvalue_hamiltonian {m : ℕ}
    (A : I → Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i, (A i).IsHermitian) (f : ℝ → ℝ) :
    (∑ k, f (ascendingEigenvalue (hamiltonian_hermitian A hA) k)) =
      ∑ s, f (spectralEnergy A hA s) := by
  have he := hermitian_eigenvalues₀_eq_of_charpoly_eq
    (hamiltonian_hermitian A hA) (isHermitian_diagonal (spectralEnergy A hA))
    (hamiltonian_charpoly A hA)
  simp only [ascendingEigenvalue, he]
  exact sum_ascendingEigenvalue_diagonal _ _ _

/-- Exact heterogeneous finite partition factorization, proved from actual spectra. -/
theorem partition_hamiltonian {m : ℕ}
    (A : I → Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i, (A i).IsHermitian) (β : ℝ) :
    (∑ k, Real.exp (-β * ascendingEigenvalue (hamiltonian_hermitian A hA) k)) =
      ∏ i, ∑ j, Real.exp (-β * FiniteOscillator.increasingValue (hA i) j) := by
  rw [sum_ascendingEigenvalue_hamiltonian A hA (fun x => Real.exp (-β * x))]
  simp only [spectralEnergy, Finset.mul_sum, Real.exp_sum]
  exact (Fintype.prod_sum (fun i (j : Fin m) => Real.exp (-β * FiniteOscillator.increasingValue (hA i) j))).symm

end BilayerDressed.FiniteProduct

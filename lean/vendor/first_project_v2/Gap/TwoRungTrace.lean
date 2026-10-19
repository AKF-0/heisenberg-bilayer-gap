import Gap.TwoRungSpectrum
import Gap.ClusterSeed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The exact two-rung matrix partition function

The trace formula is derived from the certified sixteen-dimensional matrix,
using an explicit diagonalization of its two-dimensional block. Degeneracies
between different sectors cause no loss of multiplicity.
-/

noncomputable section
namespace BilayerGap
namespace TwoRungTrace

open TwoRung TwoRungSpectrum
open scoped Matrix.Norms.Operator
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Exponential trace is unchanged by an explicitly certified similarity. -/
theorem trace_exp_eq_of_intertwines {n : Type*} [Fintype n] [DecidableEq n]
    (A D P Q : Matrix n n ℝ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hAP : A * P = P * D) (c : ℝ) :
    Matrix.trace (NormedSpace.exp ℝ (c • A)) =
      Matrix.trace (NormedSpace.exp ℝ (c • D)) := by
  let U : (Matrix n n ℝ)ˣ := ⟨P, Q, hPQ, hQP⟩
  have hconj : Q * (c • A) * P = c • D := by
    rw [mul_smul_comm, smul_mul_assoc, mul_assoc, hAP, ← mul_assoc, hQP, one_mul]
  have hexp := Matrix.exp_units_conj' ℝ U (c • A)
  change NormedSpace.exp ℝ (Q * (c • A) * P) =
    Q * NormedSpace.exp ℝ (c • A) * P at hexp
  rw [hconj] at hexp
  rw [hexp, Matrix.trace_mul_cycle, hPQ, one_mul]

/-- Reindexing preserves the exponential trace. -/
theorem trace_exp_reindex {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix m m ℝ) :
    Matrix.trace (NormedSpace.exp ℝ (Matrix.reindex e e A)) =
      Matrix.trace (NormedSpace.exp ℝ A) := by
  have hc : Continuous (Matrix.reindexAlgEquiv ℝ ℝ e) := by
    change Continuous (fun A : Matrix m m ℝ => fun i j => A (e.symm i) (e.symm j))
    fun_prop
  have he := NormedSpace.map_exp ℝ (Matrix.reindexAlgEquiv ℝ ℝ e) hc A
  simp only [Matrix.reindexAlgEquiv_apply] at he
  rw [← he]
  exact e.symm.sum_comp (fun i => (NormedSpace.exp ℝ A) i i)

/-- Explicit eigenvectors for the two-dimensional block when the coupling is nonzero. -/
def singletBasis (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3 * t / 4, 3 * t / 4; energyMinus t, energyPlus t]

theorem singlet_basis_det_ne_zero {t : ℝ} (ht : t ≠ 0) :
    (singletBasis t).det ≠ 0 := by
  rw [Matrix.det_fin_two]
  have hdiff : energyPlus t - energyMinus t ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (energyMinus_lt_energyPlus t))
  have heq : (singletBasis t) 0 0 * (singletBasis t) 1 1 -
      (singletBasis t) 0 1 * (singletBasis t) 1 0 =
      (3 * t / 4) * (energyPlus t - energyMinus t) := by
    simp [singletBasis]
    ring
  rw [heq]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) ht) (by norm_num)) hdiff

theorem singlet_basis_intertwines (t : ℝ) :
    singletBlock t * singletBasis t =
      singletBasis t * Matrix.diagonal ![energyMinus t, energyPlus t] := by
  have hs := Real.sq_sqrt (le_of_lt (TwoRungSpectrum.discriminant_pos t))
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singletBasis, singletBlock, singletRung, singletInteraction,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.map_apply,
      Rat.coe_castHom, energyMinus, energyPlus] <;>
      (first | (left; ring) | nlinarith)

/-- The two-sector diagonalization exists for every real coupling, including zero. -/
theorem singlet_diagonalization (t : ℝ) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) ℝ,
      P * Q = 1 ∧ Q * P = 1 ∧
      singletBlock t * P = P * Matrix.diagonal ![energyMinus t, energyPlus t] := by
  by_cases ht : t = 0
  · subst t
    refine ⟨1, 1, by simp, by simp, ?_⟩
    simp only [mul_one, one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [singletBlock, singletRung, singletInteraction,
        Matrix.diagonal, Matrix.map_apply, Rat.coe_castHom, energyMinus, energyPlus]
  · have hdet : IsUnit (singletBasis t).det := isUnit_iff_ne_zero.mpr
      (singlet_basis_det_ne_zero ht)
    exact ⟨singletBasis t, (singletBasis t)⁻¹,
      Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet,
      singlet_basis_intertwines t⟩

/-- The sixteen energies, with all repeated entries retained. -/
def allEnergies (t : ℝ) : BlockIndex → ℝ :=
  Sum.elim ![energyMinus t, energyPlus t] (scalarEnergies t)

/-- The certified direct-sum matrix is similar to its full diagonal energy list. -/
theorem block_diagonalization (t : ℝ) :
    ∃ P Q : Matrix BlockIndex BlockIndex ℝ,
      P * Q = 1 ∧ Q * P = 1 ∧
      Matrix.fromBlocks (singletBlock t) 0 0 (Matrix.diagonal (scalarEnergies t)) * P =
        P * Matrix.diagonal (allEnergies t) := by
  obtain ⟨P, Q, hPQ, hQP, hAP⟩ := singlet_diagonalization t
  refine ⟨Matrix.fromBlocks P 0 0 1, Matrix.fromBlocks Q 0 0 1, ?_, ?_, ?_⟩
  · simp [Matrix.fromBlocks_multiply, hPQ, Matrix.fromBlocks_one]
  · simp [Matrix.fromBlocks_multiply, hQP, Matrix.fromBlocks_one]
  · rw [allEnergies, ← Matrix.fromBlocks_diagonal]
    simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
      mul_one, one_mul, hAP]

/-- The actual matrix exponential trace is the sum over all sixteen energies. -/
theorem trace_exp_eq_energy_sum (t b : ℝ) :
    Matrix.trace (NormedSpace.exp ℝ ((-b) • realHamiltonian t)) =
      ∑ i, Real.exp (-b * allEnergies t i) := by
  have hfirst := trace_exp_eq_of_intertwines
    (realHamiltonian t) (realBlockHamiltonian t) (toReal basis) (toReal basisInverse)
    real_basis_mul_inverse real_inverse_mul_basis (real_hamiltonian_intertwines t) (-b)
  rw [hfirst]
  have hreindex := trace_exp_reindex splitEquiv.symm ((-b) • realBlockHamiltonian t)
  have hreindex_smul :
      Matrix.reindex splitEquiv.symm splitEquiv.symm ((-b) • realBlockHamiltonian t) =
        (-b) • Matrix.reindex splitEquiv.symm splitEquiv.symm (realBlockHamiltonian t) := rfl
  rw [hreindex_smul, real_block_split] at hreindex
  rw [← hreindex]
  obtain ⟨P, Q, hPQ, hQP, hAP⟩ := block_diagonalization t
  rw [trace_exp_eq_of_intertwines _ _ P Q hPQ hQP hAP (-b),
    ← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.coe_exp, ← Real.exp_eq_exp_ℝ]
  rfl

/-- Exact partition-function identity for the certified two-rung Hamiltonian.
This statement is uniform in both real coupling and real inverse temperature. -/
theorem trace_exp_eq_partition (t b : ℝ) :
    Matrix.trace (NormedSpace.exp ℝ ((-b) • realHamiltonian t)) =
      ClusterSeed.partition t b := by
  rw [trace_exp_eq_energy_sum]
  simp only [allEnergies, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  norm_num [Fin.sum_univ_succ, scalarEnergies, scalarRung, scalarInteraction,
    ClusterSeed.partition, ClusterSeed.lowerEnergy, ClusterSeed.upperEnergy,
    energyMinus, energyPlus]
  ring_nf

#print axioms trace_exp_eq_partition

end TwoRungTrace
end BilayerGap

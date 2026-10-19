import Gap.TwoRung

/-!
# Exact characteristic polynomial and spectrum of the two-rung Hamiltonian

This file continues the explicit matrix bridge in `TwoRung`. It splits the
certified block matrix into a two-dimensional block and fourteen diagonal
entries. All roots and multiplicities will be derived from its characteristic
polynomial; no desired spectral formula is an assumption.
-/

namespace BilayerGap
namespace TwoRungSpectrum

open TwoRung Polynomial

set_option maxRecDepth 10000
set_option maxHeartbeats 0

abbrev BlockIndex := Fin 2 ⊕ Fin 14

def splitEquiv : BlockIndex ≃ Fin 16 := finSumFinEquiv

def singletRung : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 0, 2]
def singletInteraction : Matrix (Fin 2) (Fin 2) ℚ := !![0, 3/4; 1, -1]

def scalarRung : Fin 14 → ℚ := ![1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]
def scalarInteraction : Fin 14 → ℚ :=
  ![-1/2, -1/2, -1/2, 1/2, 1/2, 1/2, -1/2, -1/2, -1/2, 1/2, 1/2, 1/2, 1/2, 1/2]

def splitRung : Matrix BlockIndex BlockIndex ℚ :=
  Matrix.fromBlocks singletRung 0 0 (Matrix.diagonal scalarRung)
def splitInteraction : Matrix BlockIndex BlockIndex ℚ :=
  Matrix.fromBlocks singletInteraction 0 0 (Matrix.diagonal scalarInteraction)

/-- Exact rational identification with a genuine direct-sum block matrix. -/
theorem split_rung : Matrix.reindex splitEquiv.symm splitEquiv.symm blockRung = splitRung := by
  ext (i | i) (j | j) : 2
  all_goals fin_cases i <;> fin_cases j <;> decide +kernel

/-- Exact rational interaction decomposition. -/
theorem split_interaction :
    Matrix.reindex splitEquiv.symm splitEquiv.symm blockInteraction = splitInteraction := by
  ext (i | i) (j | j) : 2
  all_goals fin_cases i <;> fin_cases j <;> decide +kernel

noncomputable def singletBlock (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  singletRung.map (Rat.castHom ℝ) + t • singletInteraction.map (Rat.castHom ℝ)

noncomputable def scalarEnergies (t : ℝ) : Fin 14 → ℝ :=
  fun i => (scalarRung i : ℝ) + t * (scalarInteraction i : ℝ)

/-- The certified real block matrix is a 2+14 direct sum. -/
theorem real_block_split (t : ℝ) :
    Matrix.reindex splitEquiv.symm splitEquiv.symm (realBlockHamiltonian t) =
      Matrix.fromBlocks (singletBlock t) 0 0 (Matrix.diagonal (scalarEnergies t)) := by
  have h0 : Matrix.reindex splitEquiv.symm splitEquiv.symm (toReal blockRung) =
      splitRung.map (Rat.castHom ℝ) := by
    change (Matrix.reindex splitEquiv.symm splitEquiv.symm blockRung).map (Rat.castHom ℝ) = _
    rw [split_rung]
  have h1 : Matrix.reindex splitEquiv.symm splitEquiv.symm (toReal blockInteraction) =
      splitInteraction.map (Rat.castHom ℝ) := by
    change (Matrix.reindex splitEquiv.symm splitEquiv.symm blockInteraction).map (Rat.castHom ℝ) = _
    rw [split_interaction]
  change Matrix.reindex splitEquiv.symm splitEquiv.symm (toReal blockRung) +
      t • Matrix.reindex splitEquiv.symm splitEquiv.symm (toReal blockInteraction) = _
  rw [h0, h1]
  ext (i | i) (j | j) : 2
  · rfl
  · simp [splitRung, splitInteraction, Matrix.fromBlocks]
  · simp [splitRung, splitInteraction, Matrix.fromBlocks]
  · by_cases h : i = j
    · subst j
      simp [splitRung, splitInteraction, Matrix.fromBlocks, scalarEnergies,
        Matrix.diagonal, Matrix.map_apply, Rat.coe_castHom]
    · simp [splitRung, splitInteraction, Matrix.fromBlocks, scalarEnergies,
        Matrix.diagonal, Matrix.map_apply, Rat.coe_castHom, h]

/-- The original Hamiltonian's characteristic polynomial is reduced to 2+14 blocks. -/
theorem charpoly_split (t : ℝ) :
    (realHamiltonian t).charpoly =
      (singletBlock t).charpoly * (Matrix.diagonal (scalarEnergies t)).charpoly := by
  rw [real_charpoly_eq_blocks, ← Matrix.charpoly_reindex splitEquiv.symm,
    real_block_split, Matrix.charpoly_fromBlocks_zero₁₂]

/-- The exact characteristic quadratic of the two-dimensional sector. -/
theorem singlet_eval (t E : ℝ) :
    (singletBlock t).charpoly.eval E =
      (E - (1 - t / 2)) ^ 2 - (1 - t + t ^ 2) := by
  rw [Matrix.eval_charpoly, Matrix.det_fin_two]
  norm_num [singletBlock, singletRung, singletInteraction, Matrix.scalar_apply,
    Matrix.diagonal, Matrix.map_apply, Rat.coe_castHom]
  ring

/-- The fourteen scalar sectors have multiplicities 3,3,3,5. -/
theorem scalar_eval (t E : ℝ) :
    (Matrix.diagonal (scalarEnergies t)).charpoly.eval E =
      (E - (1 - t / 2)) ^ 3 * (E - (1 + t / 2)) ^ 3 *
      (E - (2 - t / 2)) ^ 3 * (E - (2 + t / 2)) ^ 5 := by
  rw [Matrix.charpoly_diagonal]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  norm_num [scalarEnergies, scalarRung, scalarInteraction, Fin.prod_univ_succ]
  ring

/-- The complete exact characteristic-polynomial evaluation formula. -/
theorem eval_charpoly_formula (t E : ℝ) :
    (realHamiltonian t).charpoly.eval E =
      ((E - (1 - t / 2)) ^ 2 - (1 - t + t ^ 2)) *
      (E - (1 - t / 2)) ^ 3 * (E - (1 + t / 2)) ^ 3 *
      (E - (2 - t / 2)) ^ 3 * (E - (2 + t / 2)) ^ 5 := by
  rw [charpoly_split, Polynomial.eval_mul, singlet_eval, scalar_eval]
  ring

noncomputable def factoredPolynomial (t : ℝ) : ℝ[X] :=
  ((X - C (1 - t / 2)) ^ 2 - C (1 - t + t ^ 2)) *
    (X - C (1 - t / 2)) ^ 3 * (X - C (1 + t / 2)) ^ 3 *
    (X - C (2 - t / 2)) ^ 3 * (X - C (2 + t / 2)) ^ 5

/-- Full factorization, including the characteristic multiplicities. -/
theorem charpoly_factorization (t : ℝ) :
    (realHamiltonian t).charpoly = factoredPolynomial t := by
  apply Polynomial.funext
  intro E
  rw [eval_charpoly_formula]
  simp [factoredPolynomial]

noncomputable def energyMinus (t : ℝ) : ℝ :=
  1 - t / 2 - Real.sqrt (1 - t + t ^ 2)
noncomputable def energyPlus (t : ℝ) : ℝ :=
  1 - t / 2 + Real.sqrt (1 - t + t ^ 2)

/-- The singlet discriminant is strictly positive for every real coupling. -/
theorem discriminant_pos (t : ℝ) : 0 < 1 - t + t ^ 2 := by
  nlinarith [sq_nonneg (t - 1 / 2)]

/-- The two radical energies are distinct. -/
theorem energyMinus_lt_energyPlus (t : ℝ) : energyMinus t < energyPlus t := by
  have h := Real.sqrt_pos.2 (discriminant_pos t)
  dsimp [energyMinus, energyPlus]
  linarith

/-- Both singlet roots, with no root omitted. -/
theorem singlet_roots_iff (t E : ℝ) :
    (E - (1 - t / 2)) ^ 2 - (1 - t + t ^ 2) = 0 ↔
      E = energyMinus t ∨ E = energyPlus t := by
  have hs := Real.sq_sqrt (le_of_lt (discriminant_pos t))
  constructor
  · intro h
    have hp : (E - (1 - t / 2) - Real.sqrt (1 - t + t ^ 2)) *
        (E - (1 - t / 2) + Real.sqrt (1 - t + t ^ 2)) = 0 := by
      nlinarith [h]
    rcases mul_eq_zero.mp hp with h | h
    · right
      dsimp [energyPlus]
      linarith
    · left
      dsimp [energyMinus]
      linarith
  · rintro (rfl | rfl) <;> dsimp [energyMinus, energyPlus] <;> nlinarith

/-- Exact spectrum of the actual 16 by 16 real matrix for every real coupling. -/
theorem mem_spectrum_iff (t E : ℝ) :
    E ∈ spectrum ℝ (realHamiltonian t) ↔
      E = energyMinus t ∨ E = energyPlus t ∨
      E = 1 - t / 2 ∨ E = 1 + t / 2 ∨ E = 2 - t / 2 ∨ E = 2 + t / 2 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (realHamiltonian t).charpoly.eval E = 0 ↔ _
  rw [eval_charpoly_formula]
  simp only [mul_eq_zero]
  rw [singlet_roots_iff]
  simp only [pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0),
    pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0), sub_eq_zero]
  tauto

end TwoRungSpectrum
end BilayerGap

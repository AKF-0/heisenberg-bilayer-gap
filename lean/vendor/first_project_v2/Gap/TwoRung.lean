import Mathlib

/-!
# An explicit exact two-rung matrix decomposition

The computational basis is the lexicographic four-spin bit basis, with sites
0,1 on the first rung and sites 2,3 on the second. A spin-half exchange is
represented by `(1/2) Swap - (1/4) I`. Thus the rung part is the sum of the two
rung exchanges plus `(3/2) I`, and the perturbation is the sum of exchanges
between sites 0,2 and between sites 1,3.

Every entry of the resulting 16 by 16 rational matrices and an explicit
invertible change of basis is checked. The basis is unnormalized, so the
singlet block is `[[0,3t/4],[t,2-t]]`, not a symmetric block. Its characteristic
quadratic is `E²-(2-t)E-3t²/4`.

The identities hold for every real coupling after scalar extension. No
numerical eigensolver output is trusted. Identifying this swap representation
with abstract tensor-product spin operators and deriving partition-function
bounds from the decomposition remain separate obligations.
-/

namespace BilayerGap
namespace TwoRung
set_option maxRecDepth 10000
set_option maxHeartbeats 0
abbrev QMat := Matrix (Fin 16) (Fin 16) ℚ
abbrev RMat := Matrix (Fin 16) (Fin 16) ℝ

def swap01 : Fin 16 → Fin 16 := ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15]

def swap23 : Fin 16 → Fin 16 := ![0, 2, 1, 3, 4, 6, 5, 7, 8, 10, 9, 11, 12, 14, 13, 15]

def swap02 : Fin 16 → Fin 16 := ![0, 1, 8, 9, 4, 5, 12, 13, 2, 3, 10, 11, 6, 7, 14, 15]

def swap13 : Fin 16 → Fin 16 := ![0, 4, 2, 6, 1, 5, 3, 7, 8, 12, 10, 14, 9, 13, 11, 15]

def permutationMatrix (p : Fin 16 → Fin 16) : QMat :=
  fun i j => if i = p j then 1 else 0

def exchange (p : Fin 16 → Fin 16) : QMat :=
  (1 / 2 : ℚ) • permutationMatrix p - (1 / 4 : ℚ) • 1

/-- The two triplet projectors in the four-spin computational basis. -/
def rung : QMat :=
  !![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 3/2, 1/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1/2, 3/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 3/2, 0, 0, 0, 1/2, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1/2, 0, 0, 1/2, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1/2, 1, 0, 0, 0, 1/2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 3/2, 0, 0, 0, 1/2, 0, 0, 0, 0;
    0, 0, 0, 0, 1/2, 0, 0, 0, 3/2, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1/2, 0, 0, 0, 1, 1/2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1/2, 0, 0, 1/2, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1/2, 0, 0, 0, 3/2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3/2, 1/2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/2, 3/2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]

/-- The two intralayer nearest-neighbor exchanges. -/
def interaction : QMat :=
  !![1/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1/2, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -1/2, 0, 0, 1/2, 0, 0, 1/2, 0, 0, 0, 0, 0, 0;
    0, 1/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1/2, 0, 0, -1/2, 0, 0, 0, 0, 0, 1/2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/2, 0, 0;
    0, 0, 1/2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1/2, 0, 0, 0, 0, 0, -1/2, 0, 0, 1/2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/2, 0;
    0, 0, 0, 0, 0, 0, 1/2, 0, 0, 1/2, 0, 0, -1/2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1/2, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1/2]

/-- An explicit unnormalized rational basis, ordered by the blocks below. -/
def basis : QMat :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0;
    0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0;
    0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
    1, 1/2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    -1, 1/2, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
    -1, 1/2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 1/2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1, 0;
    0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- An explicit inverse, checked by rational matrix multiplication. -/
def basisInverse : QMat :=
  !![0, 0, 0, 0, 0, 1/4, -1/4, 0, 0, -1/4, 1/4, 0, 0, 0, 0, 0;
    0, 0, 0, -1/3, 0, 1/6, 1/6, 0, 0, 1/6, 1/6, 0, -1/3, 0, 0, 0;
    0, 1/4, -1/4, 0, -1/4, 0, 0, 0, 1/4, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1/2, 0, 0, 1/2, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1/4, 0, 0, 0, -1/4, 0, -1/4, 1/4, 0;
    0, -1/4, 1/4, 0, -1/4, 0, 0, 0, 1/4, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -1/2, 0, 0, 0, 0, 1/2, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1/4, 0, 0, 0, 1/4, 0, -1/4, 1/4, 0;
    0, -1/4, -1/4, 0, 1/4, 0, 0, 0, 1/4, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -1/2, 0, 0, 0, 0, 0, 0, 0, 0, 1/2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1/4, 0, 0, 0, -1/4, 0, 1/4, 1/4, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1/4, 1/4, 0, 1/4, 0, 0, 0, 1/4, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1/6, 0, 1/6, 1/6, 0, 0, 1/6, 1/6, 0, 1/6, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1/4, 0, 0, 0, 1/4, 0, 1/4, 1/4, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The dense rung matrix is exactly the spin-half swap Hamiltonian. -/
theorem rung_eq_exchange :
    rung = exchange swap01 + exchange swap23 + (3 / 2 : ℚ) • 1 := by
  decide +kernel

/-- The dense interaction is exactly the two intralayer exchanges. -/
theorem interaction_eq_exchange :
    interaction = exchange swap02 + exchange swap13 := by
  decide +kernel

/-- The diagonal rung component in the new basis. -/
def blockRung : QMat := Matrix.diagonal ![0, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]

/-- Only a two by two singlet block is non-diagonal. -/
def blockInteraction : QMat :=
  fun i j => if i = j then
      (![0, -1, -1/2, -1/2, -1/2, 1/2, 1/2, 1/2,
          -1/2, -1/2, -1/2, 1/2, 1/2, 1/2, 1/2, 1/2] : Fin 16 → ℚ) i
    else if i = 0 ∧ j = 1 then 3/4
    else if i = 1 ∧ j = 0 then 1
    else 0

/-- Exact rational certification of the inverse. -/
theorem basis_mul_inverse : basis * basisInverse = 1 := by
  decide +kernel

/-- The reverse inverse identity is explicitly certified too. -/
theorem inverse_mul_basis : basisInverse * basis = 1 := by
  decide +kernel

/-- In particular, the change of basis has nonzero determinant. -/
theorem basis_det_ne_zero : basis.det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse basis_mul_inverse

/-- Exact rung intertwining. -/
theorem rung_intertwines : rung * basis = basis * blockRung := by
  decide +kernel

/-- Exact interaction intertwining. -/
theorem interaction_intertwines : interaction * basis = basis * blockInteraction := by
  decide +kernel

def hamiltonian (t : ℚ) : QMat := rung + t • interaction
def blockHamiltonian (t : ℚ) : QMat := blockRung + t • blockInteraction

/-- Exact rational intertwining, uniformly in the coupling. -/
theorem hamiltonian_intertwines (t : ℚ) :
    hamiltonian t * basis = basis * blockHamiltonian t := by
  simp only [hamiltonian, blockHamiltonian, add_mul, smul_mul_assoc,
    mul_add, mul_smul_comm, rung_intertwines, interaction_intertwines]

/-- Explicit rational similarity. -/
theorem hamiltonian_conjugates (t : ℚ) :
    basisInverse * hamiltonian t * basis = blockHamiltonian t := by
  rw [mul_assoc, hamiltonian_intertwines, ← mul_assoc, inverse_mul_basis, one_mul]

/-- Scalar extension to the reals. -/
noncomputable def toReal (A : QMat) : RMat := A.map (Rat.castHom ℝ)

theorem toReal_mul (A B : QMat) : toReal (A * B) = toReal A * toReal B :=
  Matrix.map_mul

theorem toReal_one : toReal 1 = 1 := by
  simp [toReal]

noncomputable def realHamiltonian (t : ℝ) : RMat := toReal rung + t • toReal interaction

noncomputable def realBlockHamiltonian (t : ℝ) : RMat := toReal blockRung + t • toReal blockInteraction

theorem real_basis_mul_inverse : toReal basis * toReal basisInverse = 1 := by
  rw [← toReal_mul, basis_mul_inverse, toReal_one]

theorem real_inverse_mul_basis : toReal basisInverse * toReal basis = 1 := by
  rw [← toReal_mul, inverse_mul_basis, toReal_one]

theorem real_basis_det_ne_zero : (toReal basis).det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse real_basis_mul_inverse

/-- The finite-model decomposition holds for every real coupling. -/
theorem real_hamiltonian_intertwines (t : ℝ) :
    realHamiltonian t * toReal basis = toReal basis * realBlockHamiltonian t := by
  have h0 : toReal rung * toReal basis = toReal basis * toReal blockRung := by
    rw [← toReal_mul, rung_intertwines, toReal_mul]
  have h1 : toReal interaction * toReal basis = toReal basis * toReal blockInteraction := by
    rw [← toReal_mul, interaction_intertwines, toReal_mul]
  simp only [realHamiltonian, realBlockHamiltonian, add_mul, smul_mul_assoc,
    mul_add, mul_smul_comm, h0, h1]

/-- Exact real similarity, not a numerical spectrum assertion. -/
theorem real_hamiltonian_conjugates (t : ℝ) :
    toReal basisInverse * realHamiltonian t * toReal basis = realBlockHamiltonian t := by
  rw [mul_assoc, real_hamiltonian_intertwines, ← mul_assoc, real_inverse_mul_basis, one_mul]

/-- The computational-basis rung matrix is real symmetric. -/
theorem rung_symmetric : rung.transpose = rung := by
  decide +kernel

/-- The computational-basis interaction is real symmetric. -/
theorem interaction_symmetric : interaction.transpose = interaction := by
  decide +kernel

/-- Similarity transfers the full characteristic polynomial to the block matrix. -/
theorem real_charpoly_eq_blocks (t : ℝ) :
    (realHamiltonian t).charpoly = (realBlockHamiltonian t).charpoly := by
  calc
    (realHamiltonian t).charpoly =
        ((realHamiltonian t * toReal basis) * toReal basisInverse).charpoly := by
      rw [mul_assoc, real_basis_mul_inverse, mul_one]
    _ = (toReal basisInverse * (realHamiltonian t * toReal basis)).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = (realBlockHamiltonian t).charpoly := by
      rw [← mul_assoc, real_hamiltonian_conjugates]

/-- Characteristic quadratic of the non-scalar two by two block. -/
theorem singlet_quadratic (t E : ℝ) :
    E * (E - (2 - t)) - (3 * t / 4) * t =
      (E - (1 - t / 2)) ^ 2 - (1 - t + t ^ 2) := by
  ring

end TwoRung
end BilayerGap

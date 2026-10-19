import Mathlib

/-!
# Exact real rung representation of two spin-half degrees of freedom

The basis matrix W is deliberately unnormalized: Wᴴ W = 2 I and its exact
inverse is Wᴴ/2. This avoids square-root normalization without weakening any
similarity statement. The six physical spin matrices intertwine with i G,
where the explicitly defined G matrices are real antisymmetric.
-/
noncomputable section
namespace BilayerGap
namespace LocalRung
open Matrix
open scoped Kronecker
abbrev Q4 := Matrix (Fin 4) (Fin 4) ℚ
abbrev C4 := Matrix (Fin 4) (Fin 4) ℂ

def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1/2;
    1/2, 0],
    !![0, (-1/2 : ℂ)*Complex.I;
    (1/2 : ℂ)*Complex.I, 0],
    !![1/2, 0;
    0, -1/2]]

def generators : Fin 6 → Q4 :=
  ![!![0, 0, 0, -1/2;
    0, 0, -1/2, 0;
    0, 1/2, 0, 0;
    1/2, 0, 0, 0],
    !![0, 0, -1/2, 0;
    0, 0, 0, 1/2;
    1/2, 0, 0, 0;
    0, -1/2, 0, 0],
    !![0, 1/2, 0, 0;
    -1/2, 0, 0, 0;
    0, 0, 0, 1/2;
    0, 0, -1/2, 0],
    !![0, 0, 0, 1/2;
    0, 0, -1/2, 0;
    0, 1/2, 0, 0;
    -1/2, 0, 0, 0],
    !![0, 0, 1/2, 0;
    0, 0, 0, 1/2;
    -1/2, 0, 0, 0;
    0, -1/2, 0, 0],
    !![0, -1/2, 0, 0;
    1/2, 0, 0, 0;
    0, 0, 0, 1/2;
    0, 0, -1/2, 0]]

def basis : C4 := !![0, 0, 1, Complex.I;
    1, Complex.I, 0, 0;
    -1, Complex.I, 0, 0;
    0, 0, 1, -Complex.I]

def basisInverse : C4 := (1/2 : ℂ) • basisᴴ

def complexGenerator (k : Fin 6) : C4 := (generators k).map (Rat.castHom ℂ)

/-- Physical single-spin Pauli operators on the two-spin rung. -/
def physicalSpin (k : Fin 6) : C4 :=
  if k.val < 3 then
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      (pauli ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
  else
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩)

/-- Rung triplet projector in the real rung coordinates. -/
def rungDiagonal : Q4 := Matrix.diagonal ![0,1,1,1]

/-- The physical rung exchange plus its 3/4 energy shift. -/
def physicalRung : C4 :=
  (∑ a : Fin 3, physicalSpin ⟨a.val, by omega⟩ * physicalSpin ⟨a.val+3, by omega⟩)
    + (3/4 : ℂ) • 1

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem generators_antisymmetric (k : Fin 6) : (generators k).transpose = -generators k := by
  fin_cases k <;> decide +kernel

theorem generators_square_norm (k : Fin 6) :
    (generators k).transpose * generators k = (1/4 : ℚ) • 1 := by
  fin_cases k <;> decide +kernel

theorem generators_diagonal_zero (k : Fin 6) (i : Fin 4) : generators k i i = 0 := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem basis_inverse_left : basisInverse * basis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisInverse, basis, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.one_apply] <;>
    try ring_nf <;> norm_num [Complex.I_sq, pow_succ, Fin.ext_iff, Fin.succ]

theorem basis_inverse_right : basis * basisInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basisInverse, basis, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.one_apply] <;>
    try ring_nf <;> norm_num [Complex.I_sq, pow_succ, Fin.ext_iff, Fin.succ]

/-- The real generators represent the actual six single-spin operators. -/
theorem physical_spin_intertwines (k : Fin 6) :
    physicalSpin k * basis = basis * (Complex.I • complexGenerator k) := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [physicalSpin, pauli, basis, complexGenerator, generators,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kronecker_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Matrix.one_apply] <;>
    try ring_nf <;> norm_num [Complex.I_sq, pow_succ, Fin.ext_iff, Fin.succ]


#print axioms physical_spin_intertwines
#print axioms basis_inverse_left
end LocalRung
end BilayerGap

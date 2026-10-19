import Mathlib

/-!
# Exact local interaction in the singlet / Cartesian-triplet basis

The coefficient ring is arbitrary and commutative. Thus the identity is a
polynomial identity, not a test at numerical values. The factor of two keeps
all formulas integral. A physical-spin change-of-basis adapter is still needed.
-/

noncomputable section
open scoped BigOperators Kronecker

set_option maxHeartbeats 2000000

namespace BilayerDressed.LocalBond

variable {R : Type*} [CommRing R]

abbrev PairIndex := Fin 4 × Fin 4
abbrev Mat (R : Type*) := Matrix (Fin 4) (Fin 4) R

def unit (i j : Fin 4) : Mat R := Matrix.single i j 1
def create (α : Fin 3) : Mat R := unit α.succ 0
def annihilate (α : Fin 3) : Mat R := unit 0 α.succ
def difference (α : Fin 3) : Mat R := create α + annihilate α

/-- Twice the two-layer rung interaction, in its four-state rung basis. -/
def twiceBond : Matrix PairIndex PairIndex R :=
  (∑ α : Fin 3, difference α ⊗ₖ difference α) +
  ∑ α : Fin 3, ∑ β : Fin 3,
    (unit α.succ β.succ ⊗ₖ unit β.succ α.succ -
      unit α.succ β.succ ⊗ₖ unit α.succ β.succ)

def dot (A B : Fin 3 → R) : R := ∑ α : Fin 3, A α * B α

def coherent (A B : Fin 3 → R) (k : R) : PairIndex → R := fun p =>
  !![1, B 0, B 1, B 2;
    A 0, A 0*B 0+k, A 0*B 1, A 0*B 2;
    A 1, A 1*B 0, A 1*B 1+k, A 1*B 2;
    A 2, A 2*B 0, A 2*B 1, A 2*B 2+k] p.1 p.2

def bareAction (A B : Fin 3 → R) (k : R) : PairIndex → R := fun p =>
  !![dot A B+3*k, A 0, A 1, A 2;
    B 0, 1+B 0*A 0-dot A B-2*k, B 0*A 1, B 0*A 2;
    B 1, B 1*A 0, 1+B 1*A 1-dot A B-2*k, B 1*A 2;
    B 2, B 2*A 0, B 2*A 1, 1+B 2*A 2-dot A B-2*k] p.1 p.2

def action (v : PairIndex → R) : PairIndex → R := fun p =>
  let t := v (1,1)+v (2,2)+v (3,3)
  !![t, v (1,0), v (2,0), v (3,0);
    v (0,1), v (0,0)+v (1,1)-t, v (2,1), v (3,1);
    v (0,2), v (1,2), v (0,0)+v (2,2)-t, v (3,2);
    v (0,3), v (1,3), v (2,3), v (0,0)+v (3,3)-t] p.1 p.2

/-- Exact action of the actual sixteen-dimensional local interaction. -/
theorem twiceBond_mulVec (v : PairIndex → R) :
    Matrix.mulVec (twiceBond : Matrix PairIndex PairIndex R) v = action v := by
  ext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [twiceBond, difference, create, annihilate, unit, action,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Matrix.kronecker_apply, Matrix.single, Matrix.add_apply, Matrix.sub_apply] <;> ring

/-- The local coherent-state action is an identity over any commutative ring. -/
theorem twiceBond_coherent (A B : Fin 3 → R) (k : R) :
    Matrix.mulVec (twiceBond : Matrix PairIndex PairIndex R) (coherent A B k) =
      bareAction A B k := by
  rw [twiceBond_mulVec]
  ext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [action, coherent, bareAction, dot, Fin.sum_univ_succ] <;> ring

end BilayerDressed.LocalBond

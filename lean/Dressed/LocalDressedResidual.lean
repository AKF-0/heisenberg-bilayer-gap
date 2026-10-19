import Dressed.LocalBondAction

/-!
# Exact finite local dressing and transformed interaction

The coefficient ring may itself be a commuting hard-core creation algebra on
the other sites. The identities keep every term, including external degree
four multiplied by the two local creations (the sextic residual).
-/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace BilayerDressed.LocalBond
variable {R : Type*} [CommRing R]

def dressAction (A B : Fin 3 → R) (k : R) (v : PairIndex → R) : PairIndex → R := fun p =>
  let x := v (0,0)
  let q := fun α β : Fin 3 => v (α.succ,β.succ)+A α*v (0,β.succ)+
    B β*v (α.succ,0)+(A α*B β+if α=β then k else 0)*x
  !![x, v (0,1)+B 0*x, v (0,2)+B 1*x, v (0,3)+B 2*x;
    v (1,0)+A 0*x, q 0 0, q 0 1, q 0 2;
    v (2,0)+A 1*x, q 1 0, q 1 1, q 1 2;
    v (3,0)+A 2*x, q 2 0, q 2 1, q 2 2] p.1 p.2

/-- The exact local dressing is a genuine linear operator over its coefficient ring. -/
def dressing (A B : Fin 3 → R) (k : R) : (PairIndex → R) →ₗ[R] (PairIndex → R) where
  toFun := dressAction A B k
  map_add' := by
    intro v w
    ext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [dressAction] <;> ring
  map_smul' := by
    intro a v
    ext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [dressAction] <;> ring

/-- Changing all creation coefficients' signs gives the exact inverse. -/
theorem local_inverse_dressing (A B : Fin 3 → R) (k : R) (v : PairIndex → R) :
    dressAction (-A) (-B) (-k) (dressAction A B k v) = v := by
  ext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [dressAction] <;> ring

/-- All coefficients of twice the transformed bond, with no degree truncation. -/
def transformedCoefficients (A B : Fin 3 → R) (k : R) : PairIndex → R := fun p =>
  let c := dot A B+3*k
  let q := fun α β : Fin 3 => (if α=β then 1 else 0)+B α*A β-
    (if α=β then dot A B+2*k else 0)-A α*A β-B α*B β+
    (A α*B β-if α=β then k else 0)*c
  !![c, A 0-B 0*c, A 1-B 1*c, A 2-B 2*c;
    B 0-A 0*c, q 0 0, q 0 1, q 0 2;
    B 1-A 1*c, q 1 0, q 1 1, q 1 2;
    B 2-A 2*c, q 2 0, q 2 1, q 2 2] p.1 p.2

/-- Actual bond action followed by exact inverse dressing yields the complete
constant, quadratic, quartic and sextic coefficient formula. -/
theorem local_transformed_bond (A B : Fin 3 → R) (k : R) :
    dressAction (-A) (-B) (-k)
      (Matrix.mulVec (twiceBond : Matrix PairIndex PairIndex R) (coherent A B k)) =
        transformedCoefficients A B k := by
  rw [twiceBond_coherent]
  ext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [dressAction, bareAction, transformedCoefficients, dot, Fin.sum_univ_succ] <;> ring

end BilayerDressed.LocalBond

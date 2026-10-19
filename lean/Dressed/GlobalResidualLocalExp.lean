import Dressed.LocalDressedResidual

/-! The 16-state dressing is exactly a finite nilpotent exponential.
The coefficient algebra is commutative; there are no fermionic signs. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.LocalBond
variable {R : Type*} [CommRing R]
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- The generator before exponentiation, with at most one creation at each endpoint. -/
def generatorAction (A B : Fin 3 → R) (k : R) (v : PairIndex → R) : PairIndex → R := fun p =>
  Fin.cases (Fin.cases 0 (fun β => B β * v (0,0)) p.2)
    (fun α => Fin.cases (A α * v (0,0))
      (fun β => A α * v (0,β.succ) + B β * v (α.succ,0) +
        (if α=β then k else 0)*v (0,0)) p.2) p.1

def generator (A B : Fin 3 → R) (k : R) : Module.End R (PairIndex → R) where
  toFun := generatorAction A B k
  map_add' := by
    intro v w
    ext p
    rcases p with ⟨i,j⟩
    induction i using Fin.cases <;> induction j using Fin.cases <;> simp [generatorAction] <;> (try split_ifs) <;> ring
  map_smul' := by
    intro a v
    ext p
    rcases p with ⟨i,j⟩
    induction i using Fin.cases <;> induction j using Fin.cases <;> simp [generatorAction] <;> (try split_ifs) <;> ring

/-- Three applications cannot fit on the two hard-core endpoints. -/
theorem generator_cube_zero (A B : Fin 3 → R) (k : R) :
    (generator A B k)^3 = 0 := by
  ext v p
  rcases p with ⟨i,j⟩
  induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [pow_succ, Module.End.mul_apply, generator, generatorAction]

@[simp] theorem dressAction_ss (A B : Fin 3 → R) (k : R) (v : PairIndex → R) :
    dressAction A B k v (0,0) = v (0,0) := rfl

@[simp] theorem dressAction_ts (A B : Fin 3 → R) (k : R) (v : PairIndex → R) (α : Fin 3) :
    dressAction A B k v (α.succ,0) = v (α.succ,0) + A α*v (0,0) := by
  fin_cases α <;> simp [dressAction]

@[simp] theorem dressAction_st (A B : Fin 3 → R) (k : R) (v : PairIndex → R) (β : Fin 3) :
    dressAction A B k v (0,β.succ) = v (0,β.succ) + B β*v (0,0) := by
  fin_cases β <;> simp [dressAction]

@[simp] theorem dressAction_tt (A B : Fin 3 → R) (k : R) (v : PairIndex → R) (α β : Fin 3) :
    dressAction A B k v (α.succ,β.succ) = v (α.succ,β.succ) + A α*v (0,β.succ) +
      B β*v (α.succ,0) + (A α*B β + if α=β then k else 0)*v (0,0) := by
  fin_cases α <;> fin_cases β <;> simp [dressAction]

/-- The exact quadratic Taylor formula over a coefficient algebra. -/
theorem dressing_eq_quadratic [Algebra ℚ R] (A B : Fin 3 → R) (k : R) :
    dressing A B k = 1 + generator A B k + (1/2 : ℚ) • (generator A B k)^2 := by
  have hhalf : (algebraMap ℚ R) (1/2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
    norm_num
  ext v p
  rcases p with ⟨i,j⟩
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp [pow_succ, Module.End.mul_apply, generator, generatorAction,
      dressing, Algebra.smul_def] <;> (try split_ifs) <;>
      ring_nf <;> simp only [mul_assoc, hhalf, mul_one]

/-- No infinite series or truncation assumption is used in the dressing operator. -/
theorem dressing_eq_nilpotent_exp [Algebra ℚ R] (A B : Fin 3 → R) (k : R) :
    dressing A B k = IsNilpotent.exp (generator A B k) := by
  rw [IsNilpotent.exp_eq_sum (generator_cube_zero A B k), dressing_eq_quadratic]
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The coherent vector is the dressed two-endpoint vacuum exactly. -/
theorem dressing_vacuum (A B : Fin 3 → R) (k : R) :
    dressing A B k (Pi.single (0,0) 1) = coherent A B k := by
  ext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [dressing, dressAction, coherent]

/-- The complete local residual is reproduced by forward, not inverse, dressing. -/
theorem dressed_transformed_bond (A B : Fin 3 → R) (k : R) :
    Matrix.mulVec (twiceBond : Matrix PairIndex PairIndex R) (coherent A B k) =
      dressing A B k (transformedCoefficients A B k) := by
  have hh := local_inverse_dressing (-A) (-B) (-k)
    (Matrix.mulVec (twiceBond : Matrix PairIndex PairIndex R) (coherent A B k))
  rw [local_transformed_bond] at hh
  simpa only [neg_neg, dressing] using hh.symm

end BilayerDressed.LocalBond

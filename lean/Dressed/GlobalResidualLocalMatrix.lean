import Dressed.GlobalResidualLocalExp

/-! Matrix form of the exact local polynomial action, suitable for the genuine
outside-site creation coefficient algebra and its block algebra embedding. -/
noncomputable section
open scoped BigOperators Kronecker
namespace BilayerDressed.LocalBond
variable {R : Type*} [CommRing R]
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def generatorMatrix (A B : Fin 3 → R) (k : R) : Matrix PairIndex PairIndex R :=
  LinearMap.toMatrixAlgEquiv' (generator A B k)

def dressingMatrix (A B : Fin 3 → R) (k : R) : Matrix PairIndex PairIndex R :=
  LinearMap.toMatrixAlgEquiv' (dressing A B k)

@[simp] theorem generatorMatrix_mulVec (A B : Fin 3 → R) (k : R) (v : PairIndex → R) :
    (generatorMatrix A B k).mulVec v = generatorAction A B k v :=
by
  simpa only [generatorMatrix, LinearMap.toMatrixAlgEquiv', generator] using
    (LinearMap.toMatrix'_mulVec (generator A B k) v)

@[simp] theorem dressingMatrix_mulVec (A B : Fin 3 → R) (k : R) (v : PairIndex → R) :
    (dressingMatrix A B k).mulVec v = dressAction A B k v :=
by
  simpa only [dressingMatrix, LinearMap.toMatrixAlgEquiv', dressing] using
    (LinearMap.toMatrix'_mulVec (dressing A B k) v)

theorem generatorMatrix_cube_zero (A B : Fin 3 → R) (k : R) :
    (generatorMatrix A B k)^3=0 := by
  rw [generatorMatrix, ← map_pow, generator_cube_zero, map_zero]

theorem dressingMatrix_eq_exp [Algebra ℚ R] (A B : Fin 3 → R) (k : R) :
    dressingMatrix A B k = IsNilpotent.exp (generatorMatrix A B k) := by
  rw [dressingMatrix, dressing_eq_nilpotent_exp]
  exact IsNilpotent.map_exp ⟨3,generator_cube_zero A B k⟩ LinearMap.toMatrixAlgEquiv'

/-- The generator is the sum of the two endpoint fields and the true pair term. -/
theorem generatorMatrix_formula (A B : Fin 3 → R) (k : R) :
    generatorMatrix A B k =
      (∑ α : Fin 3, A α • ((create α : Mat R) ⊗ₖ (1 : Mat R))) +
      (∑ β : Fin 3, B β • ((1 : Mat R) ⊗ₖ (create β : Mat R))) +
      k • ∑ α : Fin 3, (create α : Mat R) ⊗ₖ (create α : Mat R) := by
  ext p q
  rcases p with ⟨i,j⟩
  rcases q with ⟨r,s⟩
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    induction r using Fin.cases <;> induction s using Fin.cases <;>
      simp [generatorMatrix, LinearMap.toMatrixAlgEquiv', LinearMap.toMatrix'_apply,
        generator, generatorAction, create, unit, Matrix.kronecker_apply,
        Matrix.one_apply, Matrix.single, Matrix.sum_apply, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, Fin.succ_inj, eq_comm]

/-- Identity on the vacuum state and creation on each of the triplet states. -/
def raise (i : Fin 4) : Mat R := Fin.cases 1 create i

def raisePair (p : PairIndex) : Matrix PairIndex PairIndex R := raise p.1 ⊗ₖ raise p.2

def creationPolynomial (v : PairIndex → R) : Matrix PairIndex PairIndex R :=
  ∑ p : PairIndex, v p • raisePair p

@[simp] theorem raise_vacuum_column (i j : Fin 4) :
    (raise i : Mat R) j 0 = if j=i then 1 else 0 := by
  induction i using Fin.cases
  · simp [raise, Matrix.one_apply]
  · simp [raise, create, unit, Matrix.single, eq_comm]

@[simp] theorem creationPolynomial_vacuum (v : PairIndex → R) :
    (creationPolynomial v).mulVec (Pi.single (0,0) 1) = v := by
  ext p
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
    creationPolynomial, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    raisePair, Matrix.kronecker_apply, raise_vacuum_column]
  simp [Fintype.sum_prod_type, mul_ite, ite_mul]

/-- The exact transformed local residual is a creation polynomial on the vacuum. -/
theorem bond_dressing_vacuum (A B : Fin 3 → R) (k : R) :
    (twiceBond * dressingMatrix A B k).mulVec (Pi.single (0,0) 1) =
      (dressingMatrix A B k * creationPolynomial (transformedCoefficients A B k)).mulVec
        (Pi.single (0,0) 1) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, creationPolynomial_vacuum,
    dressingMatrix_mulVec]
  change twiceBond.mulVec (dressing A B k (Pi.single (0,0) 1)) = _
  rw [dressing_vacuum, dressed_transformed_bond, dressingMatrix_mulVec]
  rfl

/-- An arbitrary nilpotent outside-site generator factors exactly through the
local exponential. The scalar coefficient algebra commutes with the bond. -/
theorem bond_block_exponential_vacuum [Algebra ℚ R]
    (G : R) (hG : IsNilpotent G) (A B : Fin 3 → R) (k : R) :
    (twiceBond * IsNilpotent.exp (Matrix.scalar PairIndex G + generatorMatrix A B k)).mulVec
        (Pi.single (0,0) 1) =
      (IsNilpotent.exp (Matrix.scalar PairIndex G + generatorMatrix A B k) *
        creationPolynomial (transformedCoefficients A B k)).mulVec (Pi.single (0,0) 1) := by
  have hT : IsNilpotent (generatorMatrix A B k) := ⟨3,generatorMatrix_cube_zero A B k⟩
  have hcomm := Matrix.scalar_commute G (fun _ => Commute.all _ _) (generatorMatrix A B k)
  have hf := IsNilpotent.exp_add_of_commute hcomm (hG.map (Matrix.scalar PairIndex)) hT
  have he := hG.map_exp (Matrix.scalar PairIndex)
  simp only [hf, ← he, ← dressingMatrix_eq_exp]
  have hb := (Matrix.scalar_commute (IsNilpotent.exp G) (fun _ => Commute.all _ _)
    (twiceBond : Matrix PairIndex PairIndex R)).eq
  calc
    _ = ((Matrix.scalar PairIndex (IsNilpotent.exp G)) *
        (twiceBond * dressingMatrix A B k)).mulVec (Pi.single (0,0) 1) := by
      rw [← mul_assoc, ← hb, mul_assoc]
    _ = _ := by
      rw [← Matrix.mulVec_mulVec, bond_dressing_vacuum, Matrix.mulVec_mulVec, mul_assoc]

/-- Coefficient multiplication transported by an arbitrary ring homomorphism. -/
theorem map_coefficient_smul {T : Type*} [Ring T]
    (f : Matrix PairIndex PairIndex R →+* T) (a : R) (M : Matrix PairIndex PairIndex R) :
    f (a • M) = f (Matrix.scalar PairIndex a) * f M := by
  rw [Algebra.smul_def]
  change f (Matrix.scalar PairIndex a * M) = _
  exact map_mul _ _ _

/-- Algebra-homomorphism form, with the same concrete coefficient action. -/
theorem algHom_coefficient_smul {A T : Type*} [CommSemiring A] [Ring T]
    [Algebra A R] [Algebra A T]
    (f : Matrix PairIndex PairIndex R →ₐ[A] T) (a : R) (M : Matrix PairIndex PairIndex R) :
    f (a • M) = f (Matrix.scalar PairIndex a) * f M :=
  map_coefficient_smul f.toRingHom a M

end BilayerDressed.LocalBond

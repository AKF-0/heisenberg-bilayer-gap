import Dressed.GlobalResidualLocalMatrix
import Dressed.GlobalResidualDegrees

/-! Polynomial naturality and local creation expansion for the global bridge. -/
noncomputable section
open scoped BigOperators Kronecker
namespace BilayerDressed.LocalBond
variable {R T : Type*} [CommRing R] [CommRing T]
set_option maxHeartbeats 1000000

/-- The integer bond matrix commutes with scalar extension. -/
theorem twiceBond_map (f : R →+* T) :
    (twiceBond : Matrix PairIndex PairIndex R).map f = twiceBond := by
  ext p q
  simp only [twiceBond, difference, create, annihilate, unit, Matrix.map_apply,
    Matrix.sum_apply, Matrix.kronecker_apply, Matrix.single, Matrix.add_apply,
    Matrix.sub_apply, map_sum, map_add, map_sub, map_mul]
  simp only [Matrix.kroneckerMap_apply, Matrix.add_apply, Matrix.of_apply,
    apply_ite, map_one, map_zero, map_mul, map_add]

/-- The complete coefficient polynomial commutes with ring homomorphisms. -/
theorem transformedCoefficients_map (f : R →+* T) (A B : Fin 3 → R) (k : R) :
    (fun p => f (transformedCoefficients A B k p)) =
      transformedCoefficients (fun α => f (A α)) (fun β => f (B β)) (f k) := by
  ext p
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [transformedCoefficients, dot, map_sum, map_ofNat]

/-- The creation-polynomial matrix retains all four local occupancy sectors. -/
theorem creationPolynomial_expansion (v : PairIndex → R) :
    creationPolynomial v = v (0,0) • (1 : Matrix PairIndex PairIndex R) +
      (∑ α : Fin 3, v (α.succ,0) • ((create α : Mat R) ⊗ₖ (1 : Mat R))) +
      (∑ β : Fin 3, v (0,β.succ) • ((1 : Mat R) ⊗ₖ (create β : Mat R))) +
      ∑ α : Fin 3, ∑ β : Fin 3, v (α.succ,β.succ) •
        ((create α : Mat R) ⊗ₖ (create β : Mat R)) := by
  simp only [creationPolynomial, Fintype.sum_prod_type, Fin.sum_univ_succ (n := 3),
    raisePair, raise, Fin.cases_zero, Fin.cases_succ, Matrix.one_kronecker_one,
    Finset.sum_add_distrib]
  abel

end BilayerDressed.LocalBond

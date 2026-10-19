import Gap.TorusGeometry

/-!
# Concrete regrouping of rung configurations into matched cluster factors

The equivalence uses the actual two endpoints of a perfect matching and the
lexicographic two-rung state convention. It is valid for any local pair matrix;
no change of physical on-rung basis is hidden in the permutation.
-/
noncomputable section
namespace BilayerGap
namespace Torus
open ClusterProducts Matrix
open scoped Kronecker

/-- Unpack the recursively nested cluster index into its list of local states. -/
def powerIndexEquiv : (k : ℕ) → PowerIndex k ≃ (Fin k → Fin 16)
  | 0 => {
    toFun := fun _ => Fin.elim0
    invFun := fun _ => (0 : Fin 1)
    left_inv := fun _ => Subsingleton.elim (α := Fin 1) _ _
    right_inv := fun _ => Subsingleton.elim _ _ }
  | k+1 => (Equiv.prodCongr (Equiv.refl (Fin 16)) (powerIndexEquiv k)).trans
      (Fin.consEquiv (fun _ : Fin (k+1) => Fin 16))

/-- The 16-state two-rung basis is exactly two ordered 4-state rung labels. -/
def pairStateEquiv : Fin 16 ≃ (Fin 2 → Fin 4) :=
  (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm.trans (finTwoArrowEquiv (Fin 4)).symm

/-- An arbitrary concrete perfect matching induces a true permutation of the
many-rung tensor basis. -/
def basisOfPairing {V : Type*} {k : ℕ} (e : (Fin k × Fin 2) ≃ V) :
    PowerIndex k ≃ (V → Fin 4) :=
  (powerIndexEquiv k).trans
    ((Equiv.arrowCongr (Equiv.refl _) pairStateEquiv).trans
      ((Equiv.curry (Fin k) (Fin 2) (Fin 4)).symm.trans
        (Equiv.arrowCongr e (Equiv.refl _))))

def matchingBasis (n m : ℕ) (c : Fin 4) :
    PowerIndex (PairCount n m) ≃ Config n m := basisOfPairing (matching n m c)

/-- The product singlet state, not an arbitrary basis vector. -/
def powerVacuum : (k : ℕ) → PowerIndex k
  | 0 => (0 : Fin 1)
  | k+1 => (0,powerVacuum k)

theorem powerIndexEquiv_vacuum (k : ℕ) :
    powerIndexEquiv k (powerVacuum k) = fun _ => 0 := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change powerIndexEquiv k (powerVacuum k) j = 0
      rw [ih]

theorem pairStateEquiv_zero : pairStateEquiv 0 = fun _ => 0 := by
  funext s
  fin_cases s <;> rfl

/-- All four regroupings preserve the same actual product vacuum. -/
theorem basisOfPairing_vacuum {V : Type*} {k : ℕ} (e : (Fin k × Fin 2) ≃ V) :
    basisOfPairing e (powerVacuum k) = fun _ => 0 := by
  funext v
  simp only [basisOfPairing, Equiv.trans_apply, powerIndexEquiv_vacuum]
  change pairStateEquiv 0 ((e.symm v).2) = 0
  rw [pairStateEquiv_zero]

theorem basisOfPairing_symm_vacuum {V : Type*} {k : ℕ} (e : (Fin k × Fin 2) ≃ V) :
    (basisOfPairing e).symm (fun _ => 0) = powerVacuum k := by
  apply (basisOfPairing e).injective
  simp [basisOfPairing_vacuum]

/-- The local-pair zero diagonal propagates through every independent tensor sum. -/
theorem independent_vacuum_diagonal (A : Matrix (Fin 16) (Fin 16) ℝ)
    (hA : A 0 0 = 0) (k : ℕ) :
    independentHamiltonian A k (powerVacuum k) (powerVacuum k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [independentHamiltonian, tensorSum, powerVacuum, hA, ih]

/-- This is the common zero-energy test-state diagonal used for the partition lower bound. -/
theorem reindexed_vacuum_diagonal {V : Type*} {k : ℕ} (e : (Fin k × Fin 2) ≃ V)
    (A : Matrix (Fin 16) (Fin 16) ℝ) (hA : A 0 0 = 0) :
    Matrix.reindex (basisOfPairing e) (basisOfPairing e) (independentHamiltonian A k)
      (fun _ => 0) (fun _ => 0) = 0 := by
  change independentHamiltonian A k ((basisOfPairing e).symm (fun _ => 0))
    ((basisOfPairing e).symm (fun _ => 0)) = 0
  rw [basisOfPairing_symm_vacuum]
  exact independent_vacuum_diagonal A hA k

end Torus
end BilayerGap

import Dressed.LocalBondLowerBound
import Gap.LocalRungBasis

/-!
An explicit local adapter to the real magic basis of the physical Pauli model.
Only the singlet-singlet coordinate changes sign. This is a local quadratic-form
adapter, NOT a claim that overlapping bond adapters define a global basis map.
-/
noncomputable section
namespace BilayerDressed.LocalBond
open Matrix
open scoped BigOperators Kronecker
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def magicGenerator (a : Fin 6) : Matrix (Fin 4) (Fin 4) ℝ :=
  (BilayerGap.LocalRung.generators a).map (Rat.castHom ℝ)

def magicBond : Matrix PairIndex PairIndex ℝ :=
  -(∑ a : Fin 6, magicGenerator a ⊗ₖ magicGenerator a)

def pairSign (p : PairIndex) : ℝ := if p = (0,0) then -1 else 1

def signVacuum (v : RealPair) : RealPair := fun p => pairSign p * v p

def magicBondQ : Matrix PairIndex PairIndex ℚ :=
  -(∑ a : Fin 6, BilayerGap.LocalRung.generators a ⊗ₖ BilayerGap.LocalRung.generators a)
def pairSignQ (p : PairIndex) : ℚ := if p = (0,0) then -1 else 1

/-- Exact rational identity checked by the Lean kernel, not native execution. -/
theorem magicBondQ_entry : ∀ p q : PairIndex,
    magicBondQ p q = (1/2 : ℚ)*pairSignQ p *
      (twiceBond : Matrix PairIndex PairIndex ℚ) p q *pairSignQ q := by
  decide +kernel

/-- Exact matrix identity, including the anomalous pair sign. -/
theorem magicBond_entry (p q : PairIndex) :
    magicBond p q = (1/2 : ℝ) * pairSign p *
      (twiceBond : Matrix PairIndex PairIndex ℝ) p q * pairSign q := by
  rcases p with ⟨i,j⟩
  rcases q with ⟨k,l⟩
  have hh := congrArg (fun r : ℚ => (r : ℝ)) (magicBondQ_entry (i,j) (k,l))
  simpa only [magicBondQ, magicBond, magicGenerator, pairSignQ, pairSign,
    twiceBond, difference, create, annihilate, unit, Matrix.sum_apply,
    Matrix.kronecker_apply, Matrix.single, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.neg_apply, Matrix.map_apply, Rat.cast_neg, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one,
    Rat.cast_zero, apply_ite] using hh

theorem magicBond_quadratic (v : RealPair) :
    dotProduct v (magicBond.mulVec v) =
      (1/2 : ℝ) * dotProduct (signVacuum v)
        ((twiceBond : Matrix PairIndex PairIndex ℝ).mulVec (signVacuum v)) := by
  simp only [dotProduct, Matrix.mulVec, magicBond_entry, signVacuum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem signVacuum_norm (v : RealPair) : normForm (signVacuum v) = normForm v := by
  simp [normForm, stNorm, ttNorm, offNorm, signVacuum, pairSign]

theorem signVacuum_number (v : RealPair) : numberForm (signVacuum v) = numberForm v := by
  simp [numberForm, stNorm, ttNorm, offNorm, signVacuum, pairSign]

/-- Actual physical bond lower bound in the first project's magic rung basis. -/
theorem magicBond_lower_bound (g : ℝ) (hg : 0 ≤ g) (v : RealPair) :
    -(g/2+1/20)*numberForm v-(15/2 : ℝ)*g^2*normForm v ≤
      g * dotProduct v (magicBond.mulVec v) := by
  have h := local_bond_lower_bound g hg (signVacuum v)
  rw [signVacuum_norm, signVacuum_number] at h
  rw [magicBond_quadratic]
  nlinarith only [h]

#print axioms magicBond_entry
#print axioms magicBond_lower_bound
end BilayerDressed.LocalBond

import Dressed.QuarticMatchingNorm
import Dressed.CubicPhysicalMeanEndpoints

/-! Literal quartic matching dictionaries for the physical Wick bound.
Signed canonical fiber coefficients are combined before their absolute value.
The exact color weights are 9, 3 and 3, not an independent Gaussian identity.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.QuarticPhysicalMean
open Matrix FiniteOccupation FinitePhysicalWick
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reorder a support into the two pairs selected by its matching label. -/
def pairedSites (v : Fin 4→V) (m : Fin 3) : Fin 4→V :=
  (![v, ![v 0,v 2,v 1,v 3], ![v 0,v 3,v 1,v 2]]) m

/-- The actual four creation occurrences, with one independent color per pair. -/
def matchingWords (v : Fin 4→V) (m : Fin 3) (p : Fin 3×Fin 3) : List (Mode V) :=
  [(pairedSites v m 0,p.1),(pairedSites v m 1,p.1),
   (pairedSites v m 2,p.2),(pairedSites v m 3,p.2)]

/-- Exact covariance weight of a matching, after the nine color choices. -/
def matchingWeight (L : V→V→ℝ) (v : Fin 4→V) (m : Fin 3) : ℝ :=
  let w := pairedSites v m
  9*L (w 0) (w 1)*L (w 2) (w 3)+
  3*L (w 0) (w 2)*L (w 1) (w 3)+
  3*L (w 0) (w 3)*L (w 1) (w 2)

/-- The polynomial is the literal product of physical pair creation matrices. -/
theorem matching_physicalPolynomial (v : Fin 4→V) (m : Fin 3) :
    physicalPolynomial (fun _ : Fin 3×Fin 3 => (1:ℝ)) (matchingWords v m)=
      QuarticMatching.matchingOperator v m := by
  have h : physicalPolynomial (fun _ : Fin 3×Fin 3 => (1:ℝ)) (matchingWords v m)=
      pairCreate (pairedSites v m 0) (pairedSites v m 1)*
        pairCreate (pairedSites v m 2) (pairedSites v m 3) := by
    simp [physicalPolynomial,PositiveMatrix.creationPolynomial,matchingWords,
      PositiveMatrix.word,pairCreate,Fintype.sum_prod_type,Matrix.sum_mul,Matrix.mul_sum,
      Matrix.mul_assoc]
    rw [Finset.sum_comm]
  rw [h]
  fin_cases m <;> rfl

/-- The exact 9/3/3 color count, with no distinct-site assumption. -/
theorem matching_wick_sum (L : V→V→ℝ) (v : Fin 4→V) (m : Fin 3) :
    (∑ p : Fin 3×Fin 3,FiniteWickPairings.wick
      (FiniteWick.colorLift (χ := Fin 3) L) (matchingWords v m p))=
        matchingWeight L v m := by
  simpa only [matchingWords,Fintype.sum_prod_type,matchingWeight] using
    (FiniteWickPairings.color_wick_four L (pairedSites v m 0) (pairedSites v m 1)
      (pairedSites v m 2) (pairedSites v m 3))

theorem matchingWeight_nonneg (L : V→V→ℝ) (hL : ∀ u v,0≤L u v)
    (v : Fin 4→V) (m : Fin 3) : 0 ≤ matchingWeight L v m := by
  unfold matchingWeight
  exact add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (hL _ _)) (hL _ _))
    (mul_nonneg (mul_nonneg (by norm_num) (hL _ _)) (hL _ _)))
    (mul_nonneg (mul_nonneg (by norm_num) (hL _ _)) (hL _ _))

variable {τ : Type*} [Fintype τ]

def familyCoefficients (c : τ→ℝ) (p : τ×(Fin 3×Fin 3)) : ℝ := c p.1

def familyWords (v : τ→Fin 4→V) (m : τ→Fin 3) (p : τ×(Fin 3×Fin 3)) :
    List (Mode V) := matchingWords (v p.1) (m p.1) p.2

/-- The signed coefficient is kept intact until after canonical fiber regrouping. -/
theorem family_physicalPolynomial (c : τ→ℝ) (v : τ→Fin 4→V) (m : τ→Fin 3) :
    physicalPolynomial (familyCoefficients c) (familyWords v m)=
      ∑ t,c t • QuarticMatching.matchingOperator (v t) (m t) := by
  simp only [physicalPolynomial,PositiveMatrix.creationPolynomial,Fintype.sum_prod_type,
    familyCoefficients,familyWords]
  apply Finset.sum_congr rfl
  intro t _
  rw [←matching_physicalPolynomial]
  simp only [physicalPolynomial,PositiveMatrix.creationPolynomial,one_smul,Finset.smul_sum,Fintype.sum_prod_type]

/-- Exact coefficient sum for an arbitrary family of signed matching coefficients. -/
theorem family_wick_coefficient (c : τ→ℝ) (v : τ→Fin 4→V) (m : τ→Fin 3)
    (L : V→V→ℝ) :
    (∑ p : τ×(Fin 3×Fin 3),|familyCoefficients c p| *
      FiniteWickPairings.wick (FiniteWick.colorLift (χ := Fin 3) L) (familyWords v m p))=
        ∑ t,|c t| * matchingWeight L (v t) (m t) := by
  simp only [Fintype.sum_prod_type,familyCoefficients,familyWords]
  apply Finset.sum_congr rfl
  intro t _
  rw [←matching_wick_sum]
  simp only [Fintype.sum_prod_type,Finset.mul_sum]

end BilayerDressed.QuarticPhysicalMean

import Dressed.FinitePhysicalWick

/-! Literal coefficient dictionaries for physical creation polynomials.
The ordered pair half and all three Cartesian colors are kept explicitly. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.FinitePhysicalWick
open Matrix FiniteOccupation
variable {V : Type*} [Fintype V] [DecidableEq V]

def pairCoefficients (F : Matrix V V ℝ) (p : (V×V)×Fin 3) : ℝ :=
  F p.1.1 p.1.2/2

def pairWords (p : (V×V)×Fin 3) : List (Mode V) :=
  [(p.1.1,p.2),(p.1.2,p.2)]

/-- The dictionary is the actual half-ordered hard-core pair operator. -/
theorem physicalPolynomial_pairs (F : Matrix V V ℝ) :
    physicalPolynomial (pairCoefficients F) pairWords=pairKernelS F := by
  simp only [physicalPolynomial,PositiveMatrix.creationPolynomial,Fintype.sum_prod_type,
    pairCoefficients,pairWords,PositiveMatrix.word,Matrix.mul_one]
  simp only [pairKernelS,pairKernelOperator,pairCreate,Finset.smul_sum]

/-- Exact pair mean coefficient: three colors times the ordered-pair half. -/
theorem pair_wick_coefficient (F L : Matrix V V ℝ) :
    (∑ p : (V×V)×Fin 3, |pairCoefficients F p| *
      FiniteWickPairings.wick (FiniteWick.colorLift (χ := Fin 3) L) (pairWords p))=
      (3/2 : ℝ)*∑ u,∑ v,|F u v| * L u v := by
  simp only [Fintype.sum_prod_type,pairCoefficients,pairWords,FiniteWickPairings.wick_pair,
    FiniteWick.colorLift,ite_true,abs_div,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

end BilayerDressed.FinitePhysicalWick

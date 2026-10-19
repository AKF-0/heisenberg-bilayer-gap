import Dressed.CubicResidualBernstein

/-! An exact rational-polynomial/evaluation dictionary. This is scalar algebra,
not an identification of a physical residual coefficient. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicQuarticPolynomialBridge
open Polynomial CubicResidualCoefficients

/-- Rational polynomial represented by the finite coefficient array. -/
def coefficientPolynomial {n : ℕ} (a : Fin n → ℚ) : ℚ[X] :=
  ∑ i, C (a i) * X ^ (i : ℕ)

theorem coefficientPolynomial_eval {n : ℕ} (a : Fin n → ℚ) (g : ℝ) :
    (coefficientPolynomial a).eval₂ (Rat.castHom ℝ) g = evalCoeff a g := by
  simp [coefficientPolynomial, evalCoeff, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow]

/-- Exact zero padding used for shorter residual-pair coefficient arrays. -/
def pad8 (a : Fin 8 → ℚ) : Fin 11 → ℚ :=
  ![a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, 0, 0, 0]

theorem eval_pad8 (a : Fin 8 → ℚ) (g : ℝ) : evalCoeff (pad8 a) g = evalCoeff a g := by
  simp [evalCoeff, pad8, Fin.sum_univ_succ]

end BilayerDressed.CubicQuarticPolynomialBridge

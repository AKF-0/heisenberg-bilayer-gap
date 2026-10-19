import Dressed.CubicResidualCoefficients

/-! A small exact interval certificate: rational weighted Bernstein expansions
are identities, and nonnegative coefficients prove interval nonnegativity. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualBernstein
open BilayerDressed.CubicResidualCoefficients

/-- Binomial factors are already included in the rational weights. -/
def bernsteinValue {d : ℕ} (w : Fin (d+1) → ℚ) (x : ℝ) : ℝ :=
  ∑ i,(w i : ℝ)*x^(i : ℕ)*(1-x)^(d-(i : ℕ))

 theorem bernsteinValue_nonneg {d : ℕ} (w : Fin (d+1) → ℚ)
    (hw : ∀ i,0≤w i) (x : ℝ) (hx : 0≤x) (hx1 : x≤1) :
    0≤bernsteinValue w x := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (by exact_mod_cast hw i) (pow_nonneg hx _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

/-- The polynomial identity and rational weight check are both kernel-checked
inputs. No sampling or floating-point interval premise occurs. -/
 theorem interval_nonneg {d : ℕ} (p : ℝ → ℝ) (a b : ℚ) (hab : a<b)
    (w : Fin (d+1) → ℚ) (hw : ∀ i,0≤w i)
    (heq : ∀ x,p x=bernsteinValue w ((x-(a : ℝ))/((b : ℝ)-(a : ℝ))))
    (x : ℝ) (hax : (a : ℝ)≤x) (hxb : x≤(b : ℝ)) : 0≤p x := by
  rw [heq]
  have hab' : (0 : ℝ)<(b : ℝ)-(a : ℝ) := by exact_mod_cast sub_pos.mpr hab
  apply bernsteinValue_nonneg w hw
  · exact div_nonneg (sub_nonneg.mpr hax) hab'.le
  · apply (div_le_one hab').mpr
    linarith

end BilayerDressed.CubicResidualBernstein

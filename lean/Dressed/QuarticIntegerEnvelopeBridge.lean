import Dressed.QuarticIntegerArrays

/-! A finite integer dictionary is bounded by proved real-interval envelopes.
Normalization happens after signed coefficient collection. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerEnvelope
open QuarticIntegerArrays CubicResidualCoefficients
set_option maxHeartbeats 800000

def normalized (a : Coefficients) : Fin 11→ℚ := fun k=>(a k:ℚ)/524288

theorem normalized_evaluate (a : Coefficients) (g : ℝ) :
    evalCoeff (normalized a) g=QuarticIntegerArrays.evaluate a g/524288 := by
  simp only [evalCoeff,normalized,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat,
    QuarticIntegerArrays.evaluate,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The total lookup convention also gives a valid zero envelope outside the
finite dictionary. Actual coefficient membership is certified separately. -/
def Bound (dictionary : Array Coefficients) (upper : Array ℤ) (den : ℕ) (g : ℝ) : Prop :=
  ∀ j : ℕ,|QuarticIntegerArrays.evaluate (dictionary.getD j 0) g/524288|≤
    (upper.getD j 0:ℝ)/(den:ℝ)

theorem bound_of_finite (dictionary : Array Coefficients) (upper : Array ℤ)
    (den E : ℕ) (hds : dictionary.size=E) (hus : upper.size=E) (g : ℝ)
    (hfinite : ∀ j : Fin E,
      |QuarticIntegerArrays.evaluate (dictionary.getD j.val 0) g/524288|≤
        (upper.getD j.val 0:ℝ)/(den:ℝ)) : Bound dictionary upper den g := by
  intro j
  by_cases hj : j<E
  · exact hfinite ⟨j,hj⟩
  · have hd : ¬j<dictionary.size := by simpa [hds] using hj
    have hu : ¬j<upper.size := by simpa [hus] using hj
    simp [Array.getD,hd,hu]

/-- A displayed rational envelope transfers by exact coefficient equality. -/
theorem finite_entry (a : Coefficients) (u : ℤ) (den : ℕ)
    (q : Fin 11→ℚ) (v : ℚ) (g : ℝ)
    (ha : normalized a=q) (hu : (u:ℚ)/(den:ℚ)=v)
    (hb : |evalCoeff q g|≤(v:ℝ)) :
    |QuarticIntegerArrays.evaluate a g/524288|≤(u:ℝ)/(den:ℝ) := by
  rw [←normalized_evaluate,ha]
  have hc : (u:ℝ)/(den:ℝ)=(v:ℝ) := by
    exact_mod_cast hu
  rw [hc]
  exact hb

end BilayerDressed.QuarticIntegerEnvelope

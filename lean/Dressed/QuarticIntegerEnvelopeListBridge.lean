import Dressed.QuarticIntegerEnvelopeBridge
import Dressed.CubicQuarticCoefficientBernstein

/-! Linear, exact compatibility checks for integer dictionaries and already
proved scalar envelopes. No actual graph coefficient membership is asserted. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerEnvelope
open QuarticIntegerArrays CubicQuarticCoefficientBernstein
set_option maxHeartbeats 800000

/-- A genuine zero envelope covers the dictionaries' explicit zero row. -/
def zeroEnvelope : Envelope where
  coefficients := 0
  upper := 0
  bound := by
    intro g hg hmax
    simp [CubicResidualCoefficients.evalCoeff]

/-- The recursive check consumes all three lists together, retaining order and
multiplicity. Each integer row is divided by exactly 524288, after collection. -/
def listMatches (den : ℕ) : List Coefficients → List ℤ → List Envelope → Bool
  | [], [], [] => true
  | a :: as, u :: us, e :: es =>
      decide ((∀ k, normalized a k = e.coefficients k) ∧
        (u : ℚ) / (den : ℚ) = e.upper) && listMatches den as us es
  | _, _, _ => false

/-- Exact row compatibility transfers the full real-interval bound, including
zero-default lookups outside the lists. -/
theorem list_bound_of_matches (den : ℕ) (as : List Coefficients)
    (us : List ℤ) (es : List Envelope) (h : listMatches den as us es = true)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) (j : ℕ) :
    |QuarticIntegerArrays.evaluate (as.getD j 0) g / 524288| ≤
      (us.getD j 0 : ℝ) / (den : ℝ) := by
  induction as generalizing us es j with
  | nil =>
      cases us <;> cases es <;> simp_all [listMatches]
  | cons a as ih =>
      cases us with
      | nil => simp [listMatches] at h
      | cons u us =>
          cases es with
          | nil => simp [listMatches] at h
          | cons e es =>
              simp only [listMatches, Bool.and_eq_true, decide_eq_true_eq] at h
              cases j with
              | zero =>
                  simpa only [List.getD_cons_zero] using
                    finite_entry a u den e.coefficients e.upper g
                      (funext h.1.1) h.1.2 (e.bound g hg hmax)
              | succ j =>
                  simpa only [List.getD_cons_succ] using ih us es h.2 j

/-- List-backed kernel checks imply the existing total Array lookup API. -/
theorem bound_of_list_matches (dictionary : Array Coefficients)
    (upper : Array ℤ) (den : ℕ) (es : List Envelope)
    (h : listMatches den dictionary.toList upper.toList es = true)
    (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) : Bound dictionary upper den g := by
  intro j
  simpa only [List.getD_eq_getElem?_getD, Array.getElem?_toList,
    ← Array.getD_eq_getD_getElem?] using
    list_bound_of_matches den dictionary.toList upper.toList es h g hg hmax j

end BilayerDressed.QuarticIntegerEnvelope

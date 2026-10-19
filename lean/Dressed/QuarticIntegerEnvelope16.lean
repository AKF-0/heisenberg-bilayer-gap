import Dressed.QuarticIntegerEnvelopeBridge
import Dressed.QuarticIntegerData16
import Dressed.CubicQuarticEnvelopes.Seed16

/-! Exact integer-dictionary compatibility with all43 proved scalar envelopes. -/
noncomputable section
namespace BilayerDressed.QuarticIntegerEnvelope
open QuarticIntegerArrays QuarticIntegerData CubicQuarticEnvelopes
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem dictionary16_matches : ∀ j : Fin 43,∀ k : Fin 11,
    ((dictionary16.getD j.val 0) k:ℚ)/524288=coefficients16 j k := by
  decide +kernel

theorem upper16_matches : ∀ j : Fin 43,
    (upperNumerators16.getD j.val 0:ℚ)/(upperDenominator16:ℚ)=upper16 j := by
  decide +kernel

/-- Every table dictionary entry has its certified bound on the full real interval. -/
theorem bound16 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    Bound dictionary16 upperNumerators16 upperDenominator16 g := by
  apply bound_of_finite _ _ _ 44 (by decide +kernel) (by decide +kernel)
  intro j
  by_cases hj : j.val<43
  · apply finite_entry _ _ _ (coefficients16 ⟨j.val,hj⟩) (upper16 ⟨j.val,hj⟩)
    · exact funext (dictionary16_matches ⟨j.val,hj⟩)
    · exact upper16_matches ⟨j.val,hj⟩
    · exact CubicQuarticEnvelopes.bound16 ⟨j.val,hj⟩ g hg hmax
  · have hjv : j.val=43 := by omega
    have he : j=(43 : Fin 44) := Fin.ext hjv
    rw [he]
    have hz : dictionary16.getD 43 0=(0 : Coefficients) := by decide +kernel
    have hu : upperNumerators16.getD 43 0=(0 : ℤ) := by decide +kernel
    change |QuarticIntegerArrays.evaluate (dictionary16.getD 43 0) g/524288|≤
      (upperNumerators16.getD 43 0:ℝ)/(upperDenominator16:ℝ)
    rw [hz,hu]
    simp

end BilayerDressed.QuarticIntegerEnvelope

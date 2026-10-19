import Dressed.QuarticIntegerData16
import Dressed.QuarticIntegerData32
import Dressed.QuarticIntegerNormEvaluation
import Dressed.CubicQuarticNormCertificates

/-! Literal aggregate coefficient witnesses match the independently proved
real-interval norm polynomials. Actual aggregate acceptance is separate. -/
noncomputable section
open scoped BigOperators
namespace BilayerDressed.QuarticIntegerNorm
open QuarticIntegerData CubicResidualCoefficients
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def normalized (a : NormCoefficients) : Fin 21→ℚ := fun k=>(a k:ℚ)/524288^2

theorem normalized_evaluate (a : NormCoefficients) (g : ℝ) :
    evalCoeff (normalized a) g=evaluate a g/524288^2 := by
  simp only [evalCoeff,normalized,Rat.cast_div,Rat.cast_pow,Rat.cast_intCast,Rat.cast_ofNat,
    evaluate,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem norm16_matches : normalized normNumerators16=CubicQuarticNormCertificates.coefficients16 := by
  decide +kernel

theorem norm32_matches : normalized normNumerators32=CubicQuarticNormCertificates.coefficients32 := by
  decide +kernel

theorem witness16_bound (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    evaluate normNumerators16 g/524288^2≤(ScalarTrial.F16_4:ℝ) := by
  rw [←normalized_evaluate,norm16_matches]
  exact CubicQuarticNormCertificates.bound16 g hg hmax

theorem witness32_bound (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    evaluate normNumerators32 g/524288^2≤(ScalarTrial.F32_4:ℝ) := by
  rw [←normalized_evaluate,norm32_matches]
  exact CubicQuarticNormCertificates.bound32 g hg hmax

end BilayerDressed.QuarticIntegerNorm

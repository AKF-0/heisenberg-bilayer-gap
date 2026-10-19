import Dressed.CubicQuarticEnvelopes.Batch00
import Dressed.CubicQuarticEnvelopes.Batch01


/-! Source-order displayed rational envelopes only. Physical residual polynomial
identification is a separate theorem and is not assumed or asserted here. -/
noncomputable section
namespace BilayerDressed.CubicQuarticEnvelopes
open CubicResidualCoefficients CubicQuarticCoefficientBernstein
set_option maxRecDepth 200000

def entries16 : Fin 43 → Envelope := ![envelope0000, envelope0001, envelope0002, envelope0003, envelope0004, envelope0005, envelope0006, envelope0007, envelope0008, envelope0009, envelope0010, envelope0011, envelope0012, envelope0013, envelope0014, envelope0015, envelope0016, envelope0017, envelope0018, envelope0019, envelope0020, envelope0021, envelope0022, envelope0023, envelope0024, envelope0025, envelope0026, envelope0027, envelope0028, envelope0029, envelope0030, envelope0031, envelope0032, envelope0033, envelope0034, envelope0035, envelope0036, envelope0037, envelope0038, envelope0039, envelope0040, envelope0041, envelope0042]

def coefficients16 (i : Fin 43) : Fin 11 → ℚ := (entries16 i).coefficients

def upper16 (i : Fin 43) : ℚ := (entries16 i).upper

theorem bound16 (i : Fin 43) (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |evalCoeff (coefficients16 i) g| ≤ (upper16 i : ℝ) :=
  (entries16 i).bound g hg hmax

end BilayerDressed.CubicQuarticEnvelopes

import Dressed.QuarticIntegerArrays

/-! Shared constructors avoid elaborating thousands of identical vector terms. -/
namespace BilayerDressed.QuarticIntegerData
open QuarticIntegerArrays

def row3 (a b c : ℕ) : Fin 3→ℕ := ![a,b,c]

def coeff11 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : ℤ) : Coefficients :=
  ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10]

end BilayerDressed.QuarticIntegerData

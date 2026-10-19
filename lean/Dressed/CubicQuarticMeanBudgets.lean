import Dressed.CubicResidualIntervalBounds
import Dressed.CubicSexticPhysicalMeans

/-! Exact remaining quartic mean coefficient budgets. These are scalar
definitions only, separated from the final physical assembly so coefficient
certificates can consume them without importing the final trial theorem. -/
namespace BilayerDressed.CubicQuarticSeed

/-- Exact remaining quartic coefficient budget, before multiplication by the
proved positive-state norm factor. -/
def meanBudget16 : ℚ := ScalarTrial.meanCoefficient16 -
  CubicResidualIntervalBounds.meanBound16 - CubicSexticPhysicalMeans.coefficient16

/-- Exact remaining quartic coefficient budget, before multiplication by the
proved positive-state norm factor. -/
def meanBudget32 : ℚ := ScalarTrial.meanCoefficient32 -
  CubicResidualIntervalBounds.meanBound32 - CubicSexticPhysicalMeans.coefficient32

/-- Exact remaining quartic coefficient budget, before multiplication by the
proved positive-state norm factor. -/
def meanBudget64 : ℚ := ScalarTrial.meanCoefficient64 -
  CubicResidualIntervalBounds.meanBound64 - CubicSexticPhysicalMeans.coefficient64

end BilayerDressed.CubicQuarticSeed

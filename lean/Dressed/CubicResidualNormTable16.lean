import Dressed.CubicResidualResidualTable16
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualSeedCoefficients
open BilayerGap BilayerDressed.CubicResidualCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def normTable16 : Fin 15 → ℚ :=
  ![0,0,0,0,0,0,0,0,(10875/32),(1125/32),(43227/64),(97119/256),(237825/512),(125811/256),(2455479/8192)]

theorem norm_table16 : normCoeff 2 2=normTable16 := by
  have hr : coeff 2 2=residualTable16 := funext (residual_table16)
  funext k
  simp only [normCoeff,hr]
  fin_cases k <;> decide +kernel

#check norm_table16
end BilayerDressed.CubicResidualSeedCoefficients

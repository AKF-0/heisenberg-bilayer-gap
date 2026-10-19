import Dressed.CubicResidualResidualTable32
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualSeedCoefficients
open BilayerGap BilayerDressed.CubicResidualCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def normTable32 : Fin 15 → ℚ :=
  ![0,0,0,0,0,0,0,0,(49617/128),(-3015/64),(200901/256),(891855/2048),(1352007/2048),(5319045/8192),(53424615/131072)]

theorem norm_table32 : normCoeff 4 2=normTable32 := by
  have hr : coeff 4 2=residualTable32 := funext (residual_table32)
  funext k
  simp only [normCoeff,hr]
  fin_cases k <;> decide +kernel

#check norm_table32
end BilayerDressed.CubicResidualSeedCoefficients

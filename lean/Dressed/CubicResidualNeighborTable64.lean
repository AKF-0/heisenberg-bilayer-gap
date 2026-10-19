import Dressed.CubicResidualKernelTable64
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualSeedCoefficients
open BilayerGap BilayerDressed.CubicResidualCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def neighborTable64 (q : Torus.Vertex 4 4) : Fin 3 → ℚ :=
  (![![![-1,(-1/2),(-5/16)],![0,(5/8),(5/16)],![(-1/4),(-1/8),(-5/8)],![0,(1/8),(1/16)],![0,0,(-5/32)],![0,(1/8),(1/16)],![(-1/4),(-1/8),(-5/8)],![0,(5/8),(5/16)]],
    ![![0,(5/8),(5/16)],![(-1/2),(-1/4),(-5/8)],![0,(3/8),(3/16)],![0,0,(-5/16)],![0,0,0],![0,0,(-5/16)],![0,(3/8),(3/16)],![(-1/2),(-1/4),(-5/8)]],
    ![![(-1/4),(-1/8),(-5/8)],![0,(3/8),(3/16)],![0,0,(-15/32)],![0,0,0],![0,0,0],![0,0,0],![0,0,(-15/32)],![0,(3/8),(3/16)]],
    ![![0,(1/8),(1/16)],![0,0,(-5/16)],![0,0,0],![0,0,0],![0,0,0],![0,0,0],![0,0,0],![0,0,(-5/16)]],
    ![![0,0,(-5/32)],![0,0,0],![0,0,0],![0,0,0],![0,0,0],![0,0,0],![0,0,0],![0,0,0]],
    ![![0,(1/8),(1/16)],![0,0,(-5/16)],![0,0,0],![0,0,0],![0,0,0],![0,0,0],![0,0,0],![0,0,(-5/16)]],
    ![![(-1/4),(-1/8),(-5/8)],![0,(3/8),(3/16)],![0,0,(-15/32)],![0,0,0],![0,0,0],![0,0,0],![0,0,(-15/32)],![0,(3/8),(3/16)]],
    ![![0,(5/8),(5/16)],![(-1/2),(-1/4),(-5/8)],![0,(3/8),(3/16)],![0,0,(-5/16)],![0,0,0],![0,0,(-5/16)],![0,(3/8),(3/16)],![(-1/2),(-1/4),(-5/8)]]]) q.1 q.2

theorem neighbor_table64 : ∀ q : Torus.Vertex 4 4,
    b1 4 4 q=neighborTable64 q 0 ∧ b2 4 4 q=neighborTable64 q 1 ∧
      b3 4 4 q=neighborTable64 q 2 := by
  have hk1 : k1 4 4=(fun q => kernelTable64 q 0) :=
    funext fun q => (kernel_table64 q).1
  have hk2 : k2 4 4=(fun q => kernelTable64 q 1) :=
    funext fun q => (kernel_table64 q).2.1
  have hk3 : k3 4 4=(fun q => kernelTable64 q 2) :=
    funext fun q => (kernel_table64 q).2.2
  simp only [b1,b2,b3,neighborSum,hk1,hk2,hk3]
  intro ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide +kernel

#check neighbor_table64
end BilayerDressed.CubicResidualSeedCoefficients

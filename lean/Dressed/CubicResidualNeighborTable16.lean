import Dressed.CubicResidualKernelTable16
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualSeedCoefficients
open BilayerGap BilayerDressed.CubicResidualCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def neighborTable16 (q : Torus.Vertex 2 2) : Fin 3 → ℚ :=
  (![![![-1,(-1/2),(-5/8)],![0,(3/4),(3/8)],![(-1/2),(-1/4),(-5/4)],![0,(3/4),(3/8)]],
    ![![0,(3/4),(3/8)],![(-1/2),(-1/4),(-5/4)],![0,(3/4),(3/8)],![(-1/2),(-1/4),(-5/4)]],
    ![![(-1/2),(-1/4),(-5/4)],![0,(3/4),(3/8)],![0,0,(-15/8)],![0,(3/4),(3/8)]],
    ![![0,(3/4),(3/8)],![(-1/2),(-1/4),(-5/4)],![0,(3/4),(3/8)],![(-1/2),(-1/4),(-5/4)]]]) q.1 q.2

theorem neighbor_table16 : ∀ q : Torus.Vertex 2 2,
    b1 2 2 q=neighborTable16 q 0 ∧ b2 2 2 q=neighborTable16 q 1 ∧
      b3 2 2 q=neighborTable16 q 2 := by
  have hk1 : k1 2 2=(fun q => kernelTable16 q 0) :=
    funext fun q => (kernel_table16 q).1
  have hk2 : k2 2 2=(fun q => kernelTable16 q 1) :=
    funext fun q => (kernel_table16 q).2.1
  have hk3 : k3 2 2=(fun q => kernelTable16 q 2) :=
    funext fun q => (kernel_table16 q).2.2
  simp only [b1,b2,b3,neighborSum,hk1,hk2,hk3]
  intro ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide +kernel

#check neighbor_table16
end BilayerDressed.CubicResidualSeedCoefficients

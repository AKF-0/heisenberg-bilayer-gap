import Dressed.CubicResidualConvolutionTable32
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualSeedCoefficients
open BilayerGap BilayerDressed.CubicResidualCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def residualTable32 (q : Torus.Vertex 4 2) : Fin 8 → ℚ :=
  (![![![0,0,0,0,0,0,0,0],![0,0,0,0,(-1/32),(39/128),(119/256),(1873/2048)],![0,0,0,0,-1,(1/4),(-97/128),(-105/256)],![0,0,0,0,(-1/32),(39/128),(119/256),(1873/2048)]],
    ![![0,0,0,0,(-13/64),(5/16),(113/256),(2041/2048)],![0,0,0,0,(-9/16),(3/8),(-83/128),(-95/256)],![0,0,0,0,(9/16),(-13/32),(-3/128),(83/2048)],![0,0,0,0,(-9/16),(3/8),(-83/128),(-95/256)]],
    ![![0,0,0,0,(-1/2),(1/8),(-43/64),(-45/128)],![0,0,0,0,(9/32),(9/128),(21/128),(93/256)],![0,0,0,0,(-21/16),(-3/8),(-33/32),(-15/32)],![0,0,0,0,(9/32),(9/128),(21/128),(93/256)]],
    ![![0,0,0,0,(3/32),(3/16),(41/256),(67/128)],![0,0,0,0,(-7/16),(-1/8),(-89/128),(-85/256)],![0,0,0,0,0,(35/64),(45/128),(1405/2048)],![0,0,0,0,(-7/16),(-1/8),(-89/128),(-85/256)]],
    ![![0,0,0,0,(-7/32),(-1/16),(-31/64),(-15/64)],![0,0,0,0,0,(35/128),(45/256),(1315/2048)],![0,0,0,0,0,0,(-75/128),(-75/256)],![0,0,0,0,0,(35/128),(45/256),(1315/2048)]],
    ![![0,0,0,0,(3/32),(3/16),(41/256),(67/128)],![0,0,0,0,(-7/16),(-1/8),(-89/128),(-85/256)],![0,0,0,0,0,(35/64),(45/128),(1405/2048)],![0,0,0,0,(-7/16),(-1/8),(-89/128),(-85/256)]],
    ![![0,0,0,0,(-1/2),(1/8),(-43/64),(-45/128)],![0,0,0,0,(9/32),(9/128),(21/128),(93/256)],![0,0,0,0,(-21/16),(-3/8),(-33/32),(-15/32)],![0,0,0,0,(9/32),(9/128),(21/128),(93/256)]],
    ![![0,0,0,0,(-13/64),(5/16),(113/256),(2041/2048)],![0,0,0,0,(-9/16),(3/8),(-83/128),(-95/256)],![0,0,0,0,(9/16),(-13/32),(-3/128),(83/2048)],![0,0,0,0,(-9/16),(3/8),(-83/128),(-95/256)]]]) q.1 q.2

theorem residual_table32 : ∀ q : Torus.Vertex 4 2,
    coeff 4 2 q=residualTable32 q := by
  have hk1 : k1 4 2=(fun q => kernelTable32 q 0) :=
    funext fun q => (kernel_table32 q).1
  have hk2 : k2 4 2=(fun q => kernelTable32 q 1) :=
    funext fun q => (kernel_table32 q).2.1
  have hk3 : k3 4 2=(fun q => kernelTable32 q 2) :=
    funext fun q => (kernel_table32 q).2.2
  have hb1 : b1 4 2=(fun q => neighborTable32 q 0) :=
    funext fun q => (neighbor_table32 q).1
  have hb2 : b2 4 2=(fun q => neighborTable32 q 1) :=
    funext fun q => (neighbor_table32 q).2.1
  have hb3 : b3 4 2=(fun q => neighborTable32 q 2) :=
    funext fun q => (neighbor_table32 q).2.2
  have hc2 : c2 4 2=(fun q => convolutionTable32 q 0) :=
    funext fun q => (convolution_table32 q).1
  have hc3 : c3 4 2=(fun q => convolutionTable32 q 1) :=
    funext fun q => (convolution_table32 q).2.1
  have hc4 : c4 4 2=(fun q => convolutionTable32 q 2) :=
    funext fun q => (convolution_table32 q).2.2.1
  have hc5 : c5 4 2=(fun q => convolutionTable32 q 3) :=
    funext fun q => (convolution_table32 q).2.2.2.1
  have hc6 : c6 4 2=(fun q => convolutionTable32 q 4) :=
    funext fun q => (convolution_table32 q).2.2.2.2
  simp only [coeff,hk1,hk2,hk3,hb1,hb2,hb3,hc2,hc3,hc4,hc5,hc6]
  intro ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide +kernel

#check residual_table32
end BilayerDressed.CubicResidualSeedCoefficients

import Dressed.CubicResidualNeighborTable32
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualSeedCoefficients
open BilayerGap BilayerDressed.CubicResidualCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def convolutionTable32 (q : Torus.Vertex 4 2) : Fin 5 → ℚ :=
  (![![![0,(-11/8),(-11/8),(-101/32),(-45/32)],![(5/8),(5/8),(187/64),(239/128),(2373/1024)],![0,(-3/2),(-3/2),(-189/64),(-165/128)],![(5/8),(5/8),(187/64),(239/128),(2373/1024)]],
    ![![(9/16),(9/16),(79/32),(203/128),(579/256)],![0,(-5/4),(-5/4),(-175/64),(-155/128)],![(3/8),(3/8),(47/16),(117/64),(1883/1024)],![0,(-5/4),(-5/4),(-175/64),(-155/128)]],
    ![![0,(-3/4),(-3/4),(-33/16),(-15/16)],![(3/16),(3/16),(129/64),(81/64),(411/256)],![0,(-3/4),(-3/4),(-33/16),(-15/16)],![(3/16),(3/16),(129/64),(81/64),(411/256)]],
    ![![(1/16),(1/16),1,(81/128),(343/256)],![0,(-1/4),(-1/4),(-89/64),(-85/128)],![0,0,(35/32),(45/64),(1405/1024)],![0,(-1/4),(-1/4),(-89/64),(-85/128)]],
    ![![0,(-1/8),(-1/8),(-31/32),(-15/32)],![0,0,(35/64),(45/128),(1315/1024)],![0,0,0,(-75/64),(-75/128)],![0,0,(35/64),(45/128),(1315/1024)]],
    ![![(1/16),(1/16),1,(81/128),(343/256)],![0,(-1/4),(-1/4),(-89/64),(-85/128)],![0,0,(35/32),(45/64),(1405/1024)],![0,(-1/4),(-1/4),(-89/64),(-85/128)]],
    ![![0,(-3/4),(-3/4),(-33/16),(-15/16)],![(3/16),(3/16),(129/64),(81/64),(411/256)],![0,(-3/4),(-3/4),(-33/16),(-15/16)],![(3/16),(3/16),(129/64),(81/64),(411/256)]],
    ![![(9/16),(9/16),(79/32),(203/128),(579/256)],![0,(-5/4),(-5/4),(-175/64),(-155/128)],![(3/8),(3/8),(47/16),(117/64),(1883/1024)],![0,(-5/4),(-5/4),(-175/64),(-155/128)]]]) q.1 q.2

theorem convolution_table32 : ∀ q : Torus.Vertex 4 2,
    c2 4 2 q=convolutionTable32 q 0 ∧ c3 4 2 q=convolutionTable32 q 1 ∧
      c4 4 2 q=convolutionTable32 q 2 ∧ c5 4 2 q=convolutionTable32 q 3 ∧
      c6 4 2 q=convolutionTable32 q 4 := by
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
  simp only [c2,c3,c4,c5,c6,conv,hk1,hk2,hk3,hb1,hb2,hb3]
  intro ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide +kernel

#check convolution_table32
end BilayerDressed.CubicResidualSeedCoefficients

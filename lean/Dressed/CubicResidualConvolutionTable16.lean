import Dressed.CubicResidualNeighborTable16
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualSeedCoefficients
open BilayerGap BilayerDressed.CubicResidualCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def convolutionTable16 (q : Torus.Vertex 2 2) : Fin 5 → ℚ :=
  (![![![0,(-3/2),(-3/2),(-33/8),(-15/8)],![(5/8),(5/8),(111/32),(71/32),(461/128)],![0,(-3/2),(-3/2),(-33/8),(-15/8)],![(5/8),(5/8),(111/32),(71/32),(461/128)]],
    ![![(5/8),(5/8),(111/32),(71/32),(461/128)],![0,(-3/2),(-3/2),(-33/8),(-15/8)],![(3/8),(3/8),(129/32),(81/32),(411/128)],![0,(-3/2),(-3/2),(-33/8),(-15/8)]],
    ![![0,(-3/2),(-3/2),(-33/8),(-15/8)],![(3/8),(3/8),(129/32),(81/32),(411/128)],![0,(-3/2),(-3/2),(-33/8),(-15/8)],![(3/8),(3/8),(129/32),(81/32),(411/128)]],
    ![![(5/8),(5/8),(111/32),(71/32),(461/128)],![0,(-3/2),(-3/2),(-33/8),(-15/8)],![(3/8),(3/8),(129/32),(81/32),(411/128)],![0,(-3/2),(-3/2),(-33/8),(-15/8)]]]) q.1 q.2

theorem convolution_table16 : ∀ q : Torus.Vertex 2 2,
    c2 2 2 q=convolutionTable16 q 0 ∧ c3 2 2 q=convolutionTable16 q 1 ∧
      c4 2 2 q=convolutionTable16 q 2 ∧ c5 2 2 q=convolutionTable16 q 3 ∧
      c6 2 2 q=convolutionTable16 q 4 := by
  have hk1 : k1 2 2=(fun q => kernelTable16 q 0) :=
    funext fun q => (kernel_table16 q).1
  have hk2 : k2 2 2=(fun q => kernelTable16 q 1) :=
    funext fun q => (kernel_table16 q).2.1
  have hk3 : k3 2 2=(fun q => kernelTable16 q 2) :=
    funext fun q => (kernel_table16 q).2.2
  have hb1 : b1 2 2=(fun q => neighborTable16 q 0) :=
    funext fun q => (neighbor_table16 q).1
  have hb2 : b2 2 2=(fun q => neighborTable16 q 1) :=
    funext fun q => (neighbor_table16 q).2.1
  have hb3 : b3 2 2=(fun q => neighborTable16 q 2) :=
    funext fun q => (neighbor_table16 q).2.2
  simp only [c2,c3,c4,c5,c6,conv,hk1,hk2,hk3,hb1,hb2,hb3]
  intro ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide +kernel

#check convolution_table16
end BilayerDressed.CubicResidualSeedCoefficients

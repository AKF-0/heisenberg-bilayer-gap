import Dressed.CubicResidualConvolutionTable16
noncomputable section
open scoped BigOperators
namespace BilayerDressed.CubicResidualSeedCoefficients
open BilayerGap BilayerDressed.CubicResidualCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def residualTable16 (q : Torus.Vertex 2 2) : Fin 8 → ℚ :=
  (![![![0,0,0,0,0,0,0,0],![0,0,0,0,(-1/32),(27/64),(9/16),(747/512)],![0,0,0,0,-1,(1/4),(-19/16),(-5/8)],![0,0,0,0,(-1/32),(27/64),(9/16),(747/512)]],
    ![![0,0,0,0,(-1/32),(27/64),(9/16),(747/512)],![0,0,0,0,-1,(1/4),(-19/16),(-5/8)],![0,0,0,0,(9/16),(9/64),(21/64),(111/256)],![0,0,0,0,-1,(1/4),(-19/16),(-5/8)]],
    ![![0,0,0,0,-1,(1/4),(-19/16),(-5/8)],![0,0,0,0,(9/16),(9/64),(21/64),(111/256)],![0,0,0,0,(-21/8),(-3/4),(-33/16),(-15/16)],![0,0,0,0,(9/16),(9/64),(21/64),(111/256)]],
    ![![0,0,0,0,(-1/32),(27/64),(9/16),(747/512)],![0,0,0,0,-1,(1/4),(-19/16),(-5/8)],![0,0,0,0,(9/16),(9/64),(21/64),(111/256)],![0,0,0,0,-1,(1/4),(-19/16),(-5/8)]]]) q.1 q.2

theorem residual_table16 : ∀ q : Torus.Vertex 2 2,
    coeff 2 2 q=residualTable16 q := by
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
  have hc2 : c2 2 2=(fun q => convolutionTable16 q 0) :=
    funext fun q => (convolution_table16 q).1
  have hc3 : c3 2 2=(fun q => convolutionTable16 q 1) :=
    funext fun q => (convolution_table16 q).2.1
  have hc4 : c4 2 2=(fun q => convolutionTable16 q 2) :=
    funext fun q => (convolution_table16 q).2.2.1
  have hc5 : c5 2 2=(fun q => convolutionTable16 q 3) :=
    funext fun q => (convolution_table16 q).2.2.2.1
  have hc6 : c6 2 2=(fun q => convolutionTable16 q 4) :=
    funext fun q => (convolution_table16 q).2.2.2.2
  simp only [coeff,hk1,hk2,hk3,hb1,hb2,hb3,hc2,hc3,hc4,hc5,hc6]
  intro ⟨x,y⟩
  fin_cases x <;> fin_cases y <;> decide +kernel

#check residual_table16
end BilayerDressed.CubicResidualSeedCoefficients

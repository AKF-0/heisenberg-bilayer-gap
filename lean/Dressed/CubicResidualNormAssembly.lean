import Dressed.CubicTrialSeedCriterion
import Dressed.FaithfulResidualAssembly
import Dressed.CubicSexticAction

/-! The two required physical residual-norm sums. The sextic branch is already
unconditional on the whole coupling interval. Pair/quartic bounds remain exact
displayed actual-operator inputs until their coefficient checks are connected. -/
noncomputable section
namespace BilayerDressed.CubicResidualNorm
open BilayerGap GlobalResidual CubicTrialSeed
open CubicWick.FourRegularData

theorem norm16 {g : ℝ} (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (h2 : ‖(residual2 (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g :
      ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin (dressedVector (kernel16 g))‖ ≤
        (ScalarTrial.e16_2:ℝ))
    (h4 : ‖(residual4 (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g :
      ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin (dressedVector (kernel16 g))‖ ≤
        (ScalarTrial.e16_4:ℝ)) :
    ‖(CartesianBasis.fullHamiltonian 2 2 g).toEuclideanLin (dressedVector (kernel16 g))-
      residualShift (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g •
        dressedVector (kernel16 g)‖ ≤ 10982/1000000 := by
  have hh := graph_residual_norm_le_of_components (kernel16 g)
    (cubicKernel_symmetric _ g) (Torus.xNext 2 2) (Torus.yNext 2 2)
    (Torus.xNext_ne 2 2 (by omega)) (Torus.yNext_ne 2 2 (by omega))
    g (ScalarTrial.e16_2:ℝ) (ScalarTrial.e16_4:ℝ) (ScalarTrial.e16_6:ℝ)
    h2 h4 (CubicSexticAction.residual16_norm_le g hg hmax)
  apply hh.trans
  norm_num [ScalarTrial.e16_2,ScalarTrial.e16_4,ScalarTrial.e16_6]

theorem norm32 {g : ℝ} (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (h2 : ‖(residual2 (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g :
      ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin (dressedVector (kernel32 g))‖ ≤
        (ScalarTrial.e32_2:ℝ))
    (h4 : ‖(residual4 (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g :
      ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin (dressedVector (kernel32 g))‖ ≤
        (ScalarTrial.e32_4:ℝ)) :
    ‖(CartesianBasis.fullHamiltonian 4 2 g).toEuclideanLin (dressedVector (kernel32 g))-
      residualShift (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g •
        dressedVector (kernel32 g)‖ ≤ 20172/1000000 := by
  have hh := graph_residual_norm_le_of_components (kernel32 g)
    (cubicKernel_symmetric _ g) (Torus.xNext 4 2) (Torus.yNext 4 2)
    (Torus.xNext_ne 4 2 (by omega)) (Torus.yNext_ne 4 2 (by omega))
    g (ScalarTrial.e32_2:ℝ) (ScalarTrial.e32_4:ℝ) (ScalarTrial.e32_6:ℝ)
    h2 h4 (CubicSexticAction.residual32_norm_le g hg hmax)
  apply hh.trans
  norm_num [ScalarTrial.e32_2,ScalarTrial.e32_4,ScalarTrial.e32_6]

end BilayerDressed.CubicResidualNorm

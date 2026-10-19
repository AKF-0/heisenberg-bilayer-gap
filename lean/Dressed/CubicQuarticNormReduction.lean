import Dressed.CubicResidualNormAssembly
import Dressed.QuarticDressedAction

/-! The full physical residual norm reduced to the actual quartic vacuum
certificate and the displayed pair action bound. Sextic action and all finite
quartic amplification/projection hypotheses have already been discharged. -/
noncomputable section
namespace BilayerDressed.CubicQuarticNormReduction
open BilayerGap GlobalResidual CubicTrialSeed

theorem norm16 {g : ℝ} (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (h2 : ‖(residual2 (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g :
      ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin (dressedVector (kernel16 g))‖ ≤
        (ScalarTrial.e16_2:ℝ))
    (hF : ‖(residual4 (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g :
      ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin vacuumVector‖^2 ≤
        (ScalarTrial.F16_4:ℝ)) :
    ‖(CartesianBasis.fullHamiltonian 2 2 g).toEuclideanLin (dressedVector (kernel16 g))-
      residualShift (kernel16 g) (Torus.xNext 2 2) (Torus.yNext 2 2) g •
        dressedVector (kernel16 g)‖ ≤ 10982/1000000 :=
  CubicResidualNorm.norm16 hg hmax h2 (QuarticDressedAction.residual16_norm_le g hg hmax hF)

theorem norm32 {g : ℝ} (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (h2 : ‖(residual2 (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g :
      ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin (dressedVector (kernel32 g))‖ ≤
        (ScalarTrial.e32_2:ℝ))
    (hF : ‖(residual4 (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g :
      ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin vacuumVector‖^2 ≤
        (ScalarTrial.F32_4:ℝ)) :
    ‖(CartesianBasis.fullHamiltonian 4 2 g).toEuclideanLin (dressedVector (kernel32 g))-
      residualShift (kernel32 g) (Torus.xNext 4 2) (Torus.yNext 4 2) g •
        dressedVector (kernel32 g)‖ ≤ 20172/1000000 :=
  CubicResidualNorm.norm32 hg hmax h2 (QuarticDressedAction.residual32_norm_le g hg hmax hF)

end BilayerDressed.CubicQuarticNormReduction

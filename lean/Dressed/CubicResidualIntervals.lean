import Dressed.CubicResidualIntervalCertificates
import Dressed.CubicResidualSeedCoefficients
noncomputable section
namespace BilayerDressed.CubicResidualIntervals
open BilayerGap BilayerDressed.CubicResidualCoefficients
open BilayerDressed.CubicResidualSeedCoefficients BilayerDressed.CubicResidualIntervalCertificates
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

def pairClass16 (q : Torus.Vertex 2 2) : Fin 31 :=
  (![![0,1,2,1],
    ![1,2,3,2],
    ![2,3,4,3],
    ![1,2,3,2]]) q.1 q.2

theorem pairClass16_eq : ∀ q : Torus.Vertex 2 2,
    residualTable16 q=pairPoly (pairClass16 q) := by
  decide +kernel

def envelope16 (q : Torus.Vertex 2 2) : ℚ := pairBound (pairClass16 q)

theorem rootResidual_bound16 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) (q : Torus.Vertex 2 2) :
    |CubicResidualPair.rootResidual 2 2 g q|≤(envelope16 q : ℝ) := by
  rw [rootResidual_coeff 2 2 g q,residual_table16,pairClass16_eq]
  exact pair_bound (pairClass16 q) g hg hmax

theorem normSquare_bound16 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    evalCoeff (normCoeff 2 2) g≤(ScalarTrial.F16_2 : ℝ) := by
  rw [norm_table16]
  change evalCoeff certNorm16 g≤(ScalarTrial.F16_2 : ℝ)
  exact sub_nonneg.mp (norm16_nonneg g hg hmax)

def pairClass32 (q : Torus.Vertex 4 2) : Fin 31 :=
  (![![0,5,6,5],
    ![7,8,9,8],
    ![10,11,12,11],
    ![13,14,15,14],
    ![16,17,18,17],
    ![13,14,15,14],
    ![10,11,12,11],
    ![7,8,9,8]]) q.1 q.2

theorem pairClass32_eq : ∀ q : Torus.Vertex 4 2,
    residualTable32 q=pairPoly (pairClass32 q) := by
  decide +kernel

def envelope32 (q : Torus.Vertex 4 2) : ℚ := pairBound (pairClass32 q)

theorem rootResidual_bound32 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) (q : Torus.Vertex 4 2) :
    |CubicResidualPair.rootResidual 4 2 g q|≤(envelope32 q : ℝ) := by
  rw [rootResidual_coeff 4 2 g q,residual_table32,pairClass32_eq]
  exact pair_bound (pairClass32 q) g hg hmax

theorem normSquare_bound32 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) :
    evalCoeff (normCoeff 4 2) g≤(ScalarTrial.F32_2 : ℝ) := by
  rw [norm_table32]
  change evalCoeff certNorm32 g≤(ScalarTrial.F32_2 : ℝ)
  exact sub_nonneg.mp (norm32_nonneg g hg hmax)

def pairClass64 (q : Torus.Vertex 4 4) : Fin 31 :=
  (![![0,19,20,21,16,21,20,19],
    ![19,22,23,24,25,24,23,22],
    ![20,23,26,27,28,27,26,23],
    ![21,24,27,29,30,29,27,24],
    ![16,25,28,30,0,30,28,25],
    ![21,24,27,29,30,29,27,24],
    ![20,23,26,27,28,27,26,23],
    ![19,22,23,24,25,24,23,22]]) q.1 q.2

theorem pairClass64_eq : ∀ q : Torus.Vertex 4 4,
    residualTable64 q=pairPoly (pairClass64 q) := by
  decide +kernel

def envelope64 (q : Torus.Vertex 4 4) : ℚ := pairBound (pairClass64 q)

theorem rootResidual_bound64 (g : ℝ) (hg : 0≤g) (hmax : g≤1/10) (q : Torus.Vertex 4 4) :
    |CubicResidualPair.rootResidual 4 4 g q|≤(envelope64 q : ℝ) := by
  rw [rootResidual_coeff 4 4 g q,residual_table64,pairClass64_eq]
  exact pair_bound (pairClass64 q) g hg hmax


end BilayerDressed.CubicResidualIntervals

import Dressed.SexticPhysicalMean
import Dressed.CubicEndpointMax

/-! Actual physical degree-six component means for all three cubic seed boxes.
The bounds contain no state, Wick, graph-count, or coefficient-envelope premise.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BilayerDressed.CubicSexticPhysicalMeans
open Matrix BilayerGap SeedGraphs CubicSeedChecks CubicWick.FourRegularData
open FiniteOccupation FinitePhysicalWick SexticFaithfulLift SexticPhysicalMean

/-- Fixed exact scalar component of the original whole-interval certificate. -/
def coefficient16 : ℚ := 405*(1690/64000+178671581/504222432000)^3*ScalarTrial.ell16_6

theorem six_mean16 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (sites : Fin 6→Torus.Vertex 2 2) :
    |⟪dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g),
      ((sixPolynomial GlobalResidual.C sites : GlobalResidual.creationAlgebra (Torus.Vertex 2 2)) :
        ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin
          (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M16_0:ℝ)*(405*(1690/64000+tau 11597344)^3) := by
  rw [sixPolynomial_eq_physicalPolynomial]
  have h := CubicPhysicalMeans.four_by_four_physical_mean_endpoint g hg hmax
    (fun _ : Fin 3→Fin 3 => (1:ℝ)) (sixWord sites)
  simp only [abs_one,one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (six_wick_sum_le _ (CubicPhysicalMeans.covariance_nonneg _ _ _ _ _) _
      (by norm_num [tau]) CubicEndpointMax.mode16_le sites)
    (by norm_num [ScalarTrial.M16_0]))

/-- The literal physical residual6 mean, uniformly for every real 0≤g≤.1. -/
theorem residual16_mean_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g),
      ((GlobalResidual.residual6 (cubicKernel (graph 2 2 four_by_four_conditions) g)
        (Torus.xNext 2 2) (Torus.yNext 2 2) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 2 2)) :
        ConfigurationMatrix (Torus.Vertex 2 2)).toEuclideanLin
          (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M16_0:ℝ)*(coefficient16:ℝ) := by
  have h := residual6_expect_le
    (WithLp.ofLp (dressedVector (cubicKernel (graph 2 2 four_by_four_conditions) g)))
    (cubicKernel (graph 2 2 four_by_four_conditions) g) (Torus.xNext 2 2) (Torus.yNext 2 2)
    g ((ScalarTrial.M16_0:ℝ)*(405*(1690/64000+tau 11597344)^3)) hg
    (fun sites => by rw [expect_eq_inner]; exact six_mean16 g hg hmax sites)
  rw [expect_eq_inner] at h
  have he := mul_le_mul_of_nonneg_left (CubicSexticMass.ell16_le g hg hmax)
    (by norm_num [ScalarTrial.M16_0,tau] :
      (0:ℝ) ≤ (ScalarTrial.M16_0:ℝ)*(405*(1690/64000+tau 11597344)^3))
  apply h.trans
  convert he using 1 <;> norm_num [coefficient16,tau,ScalarTrial.M16_0,ScalarTrial.ell16_6]

/-- Fixed exact scalar component of the original whole-interval certificate. -/
def coefficient32 : ℚ := 405*(1690/64000+237228149/672296576000)^3*ScalarTrial.ell32_6

theorem six_mean32 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (sites : Fin 6→Torus.Vertex 4 2) :
    |⟪dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g),
      ((sixPolynomial GlobalResidual.C sites : GlobalResidual.creationAlgebra (Torus.Vertex 4 2)) :
        ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M32_0:ℝ)*(405*(1690/64000+tau 11548632)^3) := by
  rw [sixPolynomial_eq_physicalPolynomial]
  have h := CubicPhysicalMeans.eight_by_four_physical_mean_endpoint g hg hmax
    (fun _ : Fin 3→Fin 3 => (1:ℝ)) (sixWord sites)
  simp only [abs_one,one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (six_wick_sum_le _ (CubicPhysicalMeans.covariance_nonneg _ _ _ _ _) _
      (by norm_num [tau]) CubicEndpointMax.mode32_le sites)
    (by norm_num [ScalarTrial.M32_0]))

/-- The literal physical residual6 mean, uniformly for every real 0≤g≤.1. -/
theorem residual32_mean_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g),
      ((GlobalResidual.residual6 (cubicKernel (graph 4 2 eight_by_four_conditions) g)
        (Torus.xNext 4 2) (Torus.yNext 4 2) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 4 2)) :
        ConfigurationMatrix (Torus.Vertex 4 2)).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g))⟫| ≤
      (ScalarTrial.M32_0:ℝ)*(coefficient32:ℝ) := by
  have h := residual6_expect_le
    (WithLp.ofLp (dressedVector (cubicKernel (graph 4 2 eight_by_four_conditions) g)))
    (cubicKernel (graph 4 2 eight_by_four_conditions) g) (Torus.xNext 4 2) (Torus.yNext 4 2)
    g ((ScalarTrial.M32_0:ℝ)*(405*(1690/64000+tau 11548632)^3)) hg
    (fun sites => by rw [expect_eq_inner]; exact six_mean32 g hg hmax sites)
  rw [expect_eq_inner] at h
  have he := mul_le_mul_of_nonneg_left (CubicSexticMass.ell32_le g hg hmax)
    (by norm_num [ScalarTrial.M32_0,tau] :
      (0:ℝ) ≤ (ScalarTrial.M32_0:ℝ)*(405*(1690/64000+tau 11548632)^3))
  apply h.trans
  convert he using 1 <;> norm_num [coefficient32,tau,ScalarTrial.M32_0,ScalarTrial.ell32_6]

/-- Fixed exact scalar component of the original whole-interval certificate. -/
def coefficient64 : ℚ := 405*(1685/64000+70868257/201688972800)^3*ScalarTrial.ell64_6

theorem six_mean64 (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10)
    (sites : Fin 6→Torus.Vertex 4 4) :
    |⟪dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g),
      ((sixPolynomial GlobalResidual.C sites : GlobalResidual.creationAlgebra (Torus.Vertex 4 4)) :
        ConfigurationMatrix (Torus.Vertex 4 4)).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g))⟫| ≤
      (ScalarTrial.M64_0:ℝ)*(405*(1685/64000+tau 11499920)^3) := by
  rw [sixPolynomial_eq_physicalPolynomial]
  have h := CubicPhysicalMeans.eight_by_eight_physical_mean_endpoint g hg hmax
    (fun _ : Fin 3→Fin 3 => (1:ℝ)) (sixWord sites)
  simp only [abs_one,one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (six_wick_sum_le _ (CubicPhysicalMeans.covariance_nonneg _ _ _ _ _) _
      (by norm_num [tau]) CubicEndpointMax.mode64_le sites)
    (by norm_num [ScalarTrial.M64_0]))

/-- The literal physical residual6 mean, uniformly for every real 0≤g≤.1. -/
theorem residual64_mean_le (g : ℝ) (hg : 0 ≤ g) (hmax : g ≤ 1/10) :
    |⟪dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g),
      ((GlobalResidual.residual6 (cubicKernel (graph 4 4 eight_by_eight_conditions) g)
        (Torus.xNext 4 4) (Torus.yNext 4 4) g :
        GlobalResidual.creationAlgebra (Torus.Vertex 4 4)) :
        ConfigurationMatrix (Torus.Vertex 4 4)).toEuclideanLin
          (dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g))⟫| ≤
      (ScalarTrial.M64_0:ℝ)*(coefficient64:ℝ) := by
  have h := residual6_expect_le
    (WithLp.ofLp (dressedVector (cubicKernel (graph 4 4 eight_by_eight_conditions) g)))
    (cubicKernel (graph 4 4 eight_by_eight_conditions) g) (Torus.xNext 4 4) (Torus.yNext 4 4)
    g ((ScalarTrial.M64_0:ℝ)*(405*(1685/64000+tau 11499920)^3)) hg
    (fun sites => by rw [expect_eq_inner]; exact six_mean64 g hg hmax sites)
  rw [expect_eq_inner] at h
  have he := mul_le_mul_of_nonneg_left (CubicSexticMass.ell64_le g hg hmax)
    (by norm_num [ScalarTrial.M64_0,tau] :
      (0:ℝ) ≤ (ScalarTrial.M64_0:ℝ)*(405*(1685/64000+tau 11499920)^3))
  apply h.trans
  convert he using 1 <;> norm_num [coefficient64,tau,ScalarTrial.M64_0,ScalarTrial.ell64_6]

end BilayerDressed.CubicSexticPhysicalMeans
